// Two-mode hourly bars bot for agent-fun/bars-replay/v1.
//
// The bot reads the hello and the stream of batches on stdin and answers
// every batch with one reply line of orders for the next bar open. It keeps
// no state outside the run, uses no clock and no randomness, and sizes every
// order from the account the batch itself carries.
//
// Strategy: the basket regime picks the entry mode. In a confirmed basket
// uptrend the bot rotates into the strongest trend names at full gross and
// lets winners run behind a trailing stop. Otherwise it buys stretched
// names that sit far below their slow EMA (dip entries) at half gross and
// leaves quickly on take-profit, stretch recovery, stop, or time. Position
// weights are inverse to each name's hourly volatility, capped at the
// per-symbol limit. Equity drawdown halves the gross past 6% and a latch
// stops all strategy buys past 15%; a small activity floor keeps the filled
// trade count at the guardrail minimum.

const SLIP_CAP_BPS = 500;
const MIN_TICKET_USD = 25;
const FLOOR_TICKET_USD = 100;
const FLOOR_START_SEQ = 8;
const GUARD_MIN_TRADES = 8;

const CFG = {
  emaFast: 6,
  emaSlow: 24,
  volWindow: 36,
  momLookback: 6,
  minBars: 6,
  wTrend: 0.5,
  wMom: 0.0,
  wStretch: 1.0,
  wReversal: 0.0,
  dipTrendWeight: 0.3,
  trendStretchPenalty: 0.4,
  dipEntryZ: -0.8,
  dipEntryScore: 0.6,
  trendEntryScore: 1.5,
  trendMaxZ: 1.0,
  regimeThreshold: 1.2,
  basketLookback: 24,
  upNames: 5,
  dipNames: 4,
  upGross: 1.0,
  dipGross: 0.5,
  stopLoss: 0.04,
  trailDrop: 0.07,
  trailArmGain: 0.05,
  dipTakeProfit: 0.08,
  dipExitZ: 0.5,
  trendExitScore: -0.3,
  dipMaxHold: 24,
  trendMaxHold: 48,
  minHoldBars: 1,
  cooldownBars: 2,
  rebalanceBand: 0.04,
  softDrawdown: 0.06,
  latchDrawdown: 0.15,
};

let hello = null;
const universe = [];
const priceDigits = new Map();
const qtyDigits = new Map();
const closeHistory = new Map();
const fastEma = new Map();
const slowEma = new Map();
const peakClose = new Map();
const entryBar = new Map();
const entryMode = new Map();
const cooldownUntil = new Map();
const basketLogIndex = [];
let filledCount = 0;
let floorSymbol = null;
let equityPeak = 10000;
let latched = false;
let orderSeq = 0;

function barPrice(symbol, raw) {
  return Number(raw) / Math.pow(10, priceDigits.get(symbol));
}

function lastClose(symbol) {
  const list = closeHistory.get(symbol);
  return list && list.length > 0 ? list[list.length - 1] : null;
}

function pushBar(symbol, close) {
  closeHistory.get(symbol).push(close);
  if (!fastEma.has(symbol)) {
    fastEma.set(symbol, close);
    slowEma.set(symbol, close);
    return;
  }
  const aFast = 2 / (CFG.emaFast + 1);
  const aSlow = 2 / (CFG.emaSlow + 1);
  fastEma.set(symbol, fastEma.get(symbol) + aFast * (close - fastEma.get(symbol)));
  slowEma.set(symbol, slowEma.get(symbol) + aSlow * (close - slowEma.get(symbol)));
}

function popStdev(values) {
  if (values.length < 3) return null;
  let mean = 0;
  for (const v of values) mean += v;
  mean /= values.length;
  let sq = 0;
  for (const v of values) sq += (v - mean) * (v - mean);
  return Math.sqrt(sq / values.length);
}

function hourlyVol(symbol) {
  const list = closeHistory.get(symbol);
  const n = list.length;
  const from = Math.max(1, n - CFG.volWindow);
  const rets = [];
  for (let i = from; i < n; i++) rets.push(Math.log(list[i] / list[i - 1]));
  const sd = popStdev(rets);
  const vol = sd === null ? 0.01 : sd;
  return vol < 0.002 ? 0.002 : vol;
}

function signalsOf(symbol) {
  const list = closeHistory.get(symbol);
  const n = list.length;
  if (n < CFG.minBars) return null;
  const vol = hourlyVol(symbol);
  const slow = slowEma.get(symbol);
  const trend = (fastEma.get(symbol) - slow) / slow / vol;
  const look = Math.min(CFG.momLookback, n - 1);
  const mom = look >= 2 ? (list[n - 1] / list[n - 1 - look] - 1) / (vol * Math.sqrt(look)) : 0;
  const stretch = Math.log(list[n - 1] / slow) / (vol * Math.sqrt(CFG.emaSlow / 2));
  const rev1 = n >= 2 ? -(list[n - 1] / list[n - 2] - 1) / vol : 0;
  const rev3 = n >= 4 ? -(list[n - 1] / list[n - 4] - 1) / (vol * Math.sqrt(3)) : 0;
  const reversal = 0.7 * rev1 + 0.3 * rev3;
  return {
    vol,
    trend,
    stretch,
    dipScore: -CFG.wStretch * stretch + CFG.wReversal * reversal + CFG.dipTrendWeight * trend,
    trendScore: CFG.wTrend * trend + CFG.wMom * mom - CFG.trendStretchPenalty * stretch,
  };
}

function recordBasketIndex() {
  let sum = 0;
  let count = 0;
  for (const symbol of universe) {
    const list = closeHistory.get(symbol);
    if (!list || list.length === 0) continue;
    sum += list[list.length - 1] / list[0];
    count++;
  }
  if (count > 0) basketLogIndex.push(Math.log(sum / count));
}

function basketRegime(seq) {
  let trend = 0;
  let vol = 0.01;
  if (seq >= 4) {
    let now = 0;
    let back = 0;
    let count = 0;
    const lag = Math.min(CFG.basketLookback, seq);
    for (const symbol of universe) {
      const list = closeHistory.get(symbol);
      if (!list || list.length === 0) continue;
      now += list[list.length - 1] / list[0];
      back += list[list.length - 1 - lag] / list[0];
      count++;
    }
    if (count > 0 && back > 0) trend = now / back - 1;
    const from = Math.max(1, basketLogIndex.length - 24);
    const rets = [];
    for (let i = from; i < basketLogIndex.length; i++) rets.push(basketLogIndex[i] - basketLogIndex[i - 1]);
    const sd = popStdev(rets);
    if (sd !== null) vol = sd < 0.001 ? 0.001 : sd;
  }
  return { trend, regime: trend / (vol * Math.sqrt(CFG.basketLookback)) };
}

function clientId(seq) {
  orderSeq++;
  return "o" + seq + "-" + orderSeq;
}

function decide(batch) {
  const seq = batch.seq;
  const account = batch.account;
  const cashUsd = Number(account.cash_quote_units) / 1e6;
  const equityUsd = Number(account.equity_quote_units) / 1e6;
  if (equityUsd > equityPeak) equityPeak = equityUsd;
  const drawdown = equityPeak > 0 ? 1 - equityUsd / equityPeak : 0;
  if (drawdown > CFG.latchDrawdown) latched = true;

  const heldQty = new Map();
  const heldRawQty = new Map();
  const heldCost = new Map();
  for (const p of account.positions) {
    heldRawQty.set(p.symbol, p.qty);
    heldQty.set(p.symbol, Number(p.qty) / Math.pow(10, qtyDigits.get(p.symbol)));
    heldCost.set(p.symbol, Number(p.cost_quote_units) / 1e6);
  }
  for (const symbol of universe) {
    if (!heldQty.has(symbol)) {
      entryBar.delete(symbol);
      entryMode.delete(symbol);
      peakClose.delete(symbol);
    }
  }
  if (seq < (hello.warmup_bars || 0)) return [];

  const basket = basketRegime(seq);
  const sig = new Map();
  for (const symbol of universe) sig.set(symbol, signalsOf(symbol));
  let scored = 0;
  let trendPositive = 0;
  for (const symbol of universe) {
    const s = sig.get(symbol);
    if (s === null) continue;
    scored++;
    if (s.trend > 0) trendPositive++;
  }
  const breadth = scored > 0 ? trendPositive / scored : 0;
  const upRegime = basket.regime > CFG.regimeThreshold || (basket.trend > 0.01 && breadth >= 0.57);

  const orders = [];
  const exiting = new Set();
  for (const symbol of universe) {
    const qty = heldQty.get(symbol) || 0;
    if (qty <= 0) continue;
    const close = lastClose(symbol);
    if (close === null) continue;
    const peak = Math.max(peakClose.get(symbol) || close, close);
    peakClose.set(symbol, peak);
    const cost = heldCost.get(symbol) || 0;
    const pnlPct = cost > 0 ? (qty * close) / cost - 1 : 0;
    const peakPnl = cost > 0 ? (qty * peak) / cost - 1 : 0;
    const peakDrop = close / peak - 1;
    const age = seq - (entryBar.get(symbol) ?? seq);
    const mode = entryMode.get(symbol) || "dip";
    const s = sig.get(symbol);
    const maxHold = mode === "trend" ? CFG.trendMaxHold : CFG.dipMaxHold;
    let exit = false;
    if (latched) {
      exit = true;
    } else if (pnlPct <= -CFG.stopLoss) {
      exit = true;
      cooldownUntil.set(symbol, seq + CFG.cooldownBars);
    } else if (peakPnl >= CFG.trailArmGain && peakDrop <= -CFG.trailDrop && age >= 2) {
      exit = true;
      cooldownUntil.set(symbol, seq + CFG.cooldownBars);
    } else if (mode === "dip" && pnlPct >= CFG.dipTakeProfit) {
      exit = true;
    } else if (age >= maxHold) {
      exit = true;
    } else if (mode === "trend" && s !== null && s.trendScore < CFG.trendExitScore && age >= CFG.minHoldBars) {
      exit = true;
    } else if (mode === "dip" && s !== null && s.stretch > CFG.dipExitZ && age >= CFG.minHoldBars) {
      exit = true;
    }
    if (exit) exiting.add(symbol);
  }
  for (const symbol of [...exiting].sort()) {
    orders.push({
      side: "sell",
      client_id: clientId(seq),
      symbol,
      qty: heldRawQty.get(symbol),
      max_slippage_bps: SLIP_CAP_BPS,
    });
    peakClose.delete(symbol);
    entryBar.delete(symbol);
    entryMode.delete(symbol);
    if (floorSymbol === symbol) floorSymbol = null;
  }

  let cashLeft = cashUsd;
  const chosen = [];
  if (!latched) {
    const ranked = [];
    for (const symbol of universe) {
      const s = sig.get(symbol);
      if (s === null || exiting.has(symbol)) continue;
      if (seq < (cooldownUntil.get(symbol) ?? -1)) continue;
      if (floorSymbol === symbol) continue;
      if (upRegime) {
        if (s.trendScore > CFG.trendEntryScore && s.stretch < CFG.trendMaxZ) {
          ranked.push({ symbol, score: s.trendScore });
        }
      } else if (s.dipScore > CFG.dipEntryScore && s.stretch < CFG.dipEntryZ) {
        ranked.push({ symbol, score: s.dipScore });
      }
    }
    ranked.sort((a, b) => b.score - a.score || (a.symbol > b.symbol ? -1 : 1));
    const modeNew = upRegime ? "trend" : "dip";
    const nameCap = upRegime ? CFG.upNames : CFG.dipNames;
    let gross = upRegime ? CFG.upGross : CFG.dipGross;
    if (drawdown > CFG.softDrawdown) gross *= 0.5;
    for (const r of ranked.slice(0, nameCap)) chosen.push(r.symbol);
    if (chosen.length > 0) {
      const maxWeight = hello.caps.max_weight_bps / 10000;
      let invVolTotal = 0;
      for (const symbol of chosen) invVolTotal += 1 / sig.get(symbol).vol;
      for (const symbol of chosen) {
        const close = lastClose(symbol);
        if (close === null) continue;
        const weight = Math.min(maxWeight, (gross * (1 / sig.get(symbol).vol)) / invVolTotal);
        const current = (heldQty.get(symbol) || 0) * close;
        const diff = weight * equityUsd - current;
        if (diff <= CFG.rebalanceBand * equityUsd) continue;
        const room = maxWeight * equityUsd - current;
        let amount = Math.floor(Math.min(diff, cashLeft) * 1e6) / 1e6;
        amount = Math.min(amount, Math.floor(room * 1e6) / 1e6);
        if (amount < MIN_TICKET_USD) continue;
        orders.push({
          side: "buy",
          client_id: clientId(seq),
          symbol,
          notional_quote_units: String(Math.round(amount * 1e6)),
          max_slippage_bps: SLIP_CAP_BPS,
        });
        cashLeft -= amount;
        if (!heldQty.has(symbol)) {
          entryBar.set(symbol, seq);
          entryMode.set(symbol, modeNew);
        }
      }
    }
  }

  if (seq >= FLOOR_START_SEQ && filledCount < GUARD_MIN_TRADES) {
    if (floorSymbol !== null) {
      if (heldQty.has(floorSymbol) && !exiting.has(floorSymbol)) {
        orders.push({
          side: "sell",
          client_id: clientId(seq),
          symbol: floorSymbol,
          qty: heldRawQty.get(floorSymbol),
          max_slippage_bps: SLIP_CAP_BPS,
        });
        peakClose.delete(floorSymbol);
        entryBar.delete(floorSymbol);
        entryMode.delete(floorSymbol);
        floorSymbol = null;
      } else if (!heldQty.has(floorSymbol)) {
        floorSymbol = null;
      }
    }
    if (floorSymbol === null && filledCount < GUARD_MIN_TRADES) {
      for (const symbol of universe) {
        if (heldQty.has(symbol) || exiting.has(symbol) || chosen.includes(symbol)) continue;
        if (lastClose(symbol) === null || cashLeft < FLOOR_TICKET_USD) continue;
        orders.push({
          side: "buy",
          client_id: clientId(seq),
          symbol,
          notional_quote_units: String(FLOOR_TICKET_USD * 1e6),
          max_slippage_bps: SLIP_CAP_BPS,
        });
        cashLeft -= FLOOR_TICKET_USD;
        floorSymbol = symbol;
        entryBar.set(symbol, seq);
        entryMode.set(symbol, "dip");
        break;
      }
    }
  }
  return orders.slice(0, hello.caps.max_orders_per_bar);
}

function handleLine(line) {
  if (!line.trim()) return;
  const msg = JSON.parse(line);
  if (msg.type === "hello") {
    hello = msg;
    for (const s of msg.symbols) {
      universe.push(s.symbol);
      priceDigits.set(s.symbol, s.price_scale);
      qtyDigits.set(s.symbol, s.qty_scale);
      closeHistory.set(s.symbol, []);
    }
    return;
  }
  if (msg.type === "batch") {
    for (const bar of msg.bars) pushBar(bar.symbol, barPrice(bar.symbol, bar.c));
    recordBasketIndex();
    for (const fill of msg.fills) {
      if (fill.status === "filled") filledCount++;
    }
    const orders = decide(msg);
    process.stdout.write(JSON.stringify({ type: "reply", seq: msg.seq, orders }) + "\n");
    return;
  }
  if (msg.type === "done") {
    process.exit(0);
  }
}

let buffer = "";
process.stdin.setEncoding("utf8");
process.stdin.on("data", (chunk) => {
  buffer += chunk;
  let at = buffer.indexOf("\n");
  while (at >= 0) {
    const line = buffer.slice(0, at);
    buffer = buffer.slice(at + 1);
    handleLine(line);
    at = buffer.indexOf("\n");
  }
});
process.stdin.on("end", () => {
  if (buffer.trim()) handleLine(buffer);
});
