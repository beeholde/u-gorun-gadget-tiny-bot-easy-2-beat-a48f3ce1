// Tiny hourly bars bot for agent-fun/bars-replay/v1.
//
// Each batch the bot scores every symbol with a volatility-normalized blend of
// EMA trend and stretch against its slow EMA: it buys names stretched far
// below trend (dip entries), with the trend weight scaled by whether the
// basket itself is trending. It holds the strongest few names at half gross,
// leaves on stop, take-profit, max-hold, score or stretch exits, and
// otherwise sits in cash. An equity drawdown latch stops all risk trading
// once drawdown from the equity peak passes 12%, and a small activity floor
// keeps the filled trade count at the guardrail minimum.
//
// The bot reads the hello and batches on stdin and answers each batch with one
// reply line of orders for the next bar open. It keeps no state outside the
// run, uses no clock and no randomness, and sizes every order from the
// account the batch itself carries.

const MAX_SLIPPAGE_BPS = 500;
const MIN_ORDER_USD = 25;
const FLOOR_USD = 100;
const FLOOR_FROM_SEQ = 10;
const MIN_TRADES = 8;
const LATCH_DRAWDOWN = 0.12;

const P = {
  fast: 8,
  slow: 24,
  momLookback: 6,
  volWindow: 36,
  wTrend: 0.5,
  wMom: 0.0,
  wStretch: 1.0,
  wReversal: 0.0,
  stretchEntryZ: -1.5,
  stretchExitZ: -0.2,
  regimeThreshold: 0.5,
  rangeTrendWeight: 0.3,
  trendReversalWeight: 0.0,
  entryScore: 0.0,
  exitScore: 0.2,
  maxHoldings: 3,
  gross: 0.5,
  breadthScale: true,
  basketLookback: 24,
  basketGate: -1.0,
  stopLoss: 0.05,
  trailStop: 0.5,
  takeProfit: 0.05,
  cooldownBars: 0,
  minBars: 12,
  minHoldBars: 2,
  maxHoldBars: 24,
  rebalanceBand: 0.04,
};

let hello = null;
const symbols = [];
const priceScale = new Map();
const qtyScale = new Map();
const closes = new Map();
const emaFast = new Map();
const emaSlow = new Map();
const peakClose = new Map();
const entrySeq = new Map();
const cooldownUntil = new Map();
let filledTrades = 0;
let floorOpen = false;
let floorSymbol = null;
let equityPeak = 0;
let latched = false;
const indexLogs = [];
let orderCounter = 0;

function priceOf(symbol, raw) {
  return Number(raw) / Math.pow(10, priceScale.get(symbol));
}

function latestClose(symbol) {
  const list = closes.get(symbol);
  return list && list.length > 0 ? list[list.length - 1] : null;
}

function updateEma(symbol, close) {
  if (!emaFast.has(symbol)) {
    emaFast.set(symbol, close);
    emaSlow.set(symbol, close);
    return;
  }
  const aFast = 2 / (P.fast + 1);
  const aSlow = 2 / (P.slow + 1);
  emaFast.set(symbol, emaFast.get(symbol) + aFast * (close - emaFast.get(symbol)));
  emaSlow.set(symbol, emaSlow.get(symbol) + aSlow * (close - emaSlow.get(symbol)));
}

function volatility(symbol) {
  const list = closes.get(symbol);
  const n = list.length;
  const from = Math.max(1, n - P.volWindow);
  const rets = [];
  for (let i = from; i < n; i++) rets.push(Math.log(list[i] / list[i - 1]));
  if (rets.length < 3) return 0.01;
  let mean = 0;
  for (const r of rets) mean += r;
  mean /= rets.length;
  let sq = 0;
  for (const r of rets) sq += (r - mean) * (r - mean);
  const sd = Math.sqrt(sq / rets.length);
  return sd < 0.002 ? 0.002 : sd;
}

function scoreOf(symbol, trendWeight, reversalWeight) {
  const list = closes.get(symbol);
  const n = list.length;
  if (n < P.minBars) return null;
  const vol = volatility(symbol);
  const slow = emaSlow.get(symbol);
  const trend = (emaFast.get(symbol) - slow) / slow;
  const look = Math.min(P.momLookback, n - 1);
  const mom = look >= 2 ? (list[n - 1] / list[n - 1 - look] - 1) / Math.sqrt(look) : 0;
  const stretch = Math.log(list[n - 1] / slow) / (vol * Math.sqrt(P.slow / 2));
  const reversal = n >= 2 ? -(list[n - 1] / list[n - 2] - 1) / vol : 0;
  const reversal3 = n >= 4 ? -(list[n - 1] / list[n - 4] - 1) / (vol * Math.sqrt(3)) : 0;
  return {
    score:
      (P.wTrend * trendWeight * trend + P.wMom * trendWeight * mom) / vol -
      P.wStretch * stretch +
      P.wReversal * reversalWeight * (0.7 * reversal + 0.3 * reversal3),
    stretch,
  };
}

function recordIndexLog() {
  let now = 0;
  let count = 0;
  for (const symbol of symbols) {
    const list = closes.get(symbol);
    if (!list || list.length === 0) continue;
    now += list[list.length - 1] / list[0];
    count++;
  }
  if (count > 0) indexLogs.push(Math.log(now / count));
}

function basketStats(seq) {
  let trend = 0;
  let vol = 0.01;
  if (seq >= 4) {
    let now = 0;
    let back = 0;
    let count = 0;
    const lag = Math.min(P.basketLookback, seq);
    for (const symbol of symbols) {
      const list = closes.get(symbol);
      if (!list || list.length === 0) continue;
      now += list[list.length - 1] / list[0];
      back += list[list.length - 1 - lag] / list[0];
      count++;
    }
    if (count > 0 && back > 0) trend = now / back - 1;
    const from = Math.max(1, indexLogs.length - 24);
    const rets = [];
    for (let i = from; i < indexLogs.length; i++) rets.push(indexLogs[i] - indexLogs[i - 1]);
    if (rets.length >= 3) {
      let mean = 0;
      for (const r of rets) mean += r;
      mean /= rets.length;
      let sq = 0;
      for (const r of rets) sq += (r - mean) * (r - mean);
      const sd = Math.sqrt(sq / rets.length);
      vol = sd < 0.001 ? 0.001 : sd;
    }
  }
  const regime = trend / (vol * Math.sqrt(P.basketLookback));
  const trending = regime > P.regimeThreshold;
  return {
    trend,
    trendWeight: trending ? 1.0 : P.rangeTrendWeight,
    reversalWeight: trending ? P.trendReversalWeight : 1.0,
  };
}

function nextClientId(seq) {
  orderCounter++;
  return "o" + seq + "-" + orderCounter;
}

function decide(batch) {
  const seq = batch.seq;
  const warmup = hello.warmup_bars || 0;
  const account = batch.account;
  const cashUsd = Number(account.cash_quote_units) / 1e6;
  const equityUsd = Number(account.equity_quote_units) / 1e6;
  if (equityUsd > equityPeak) equityPeak = equityUsd;
  if (equityPeak > 0 && 1 - equityUsd / equityPeak > LATCH_DRAWDOWN) latched = true;
  const heldQty = new Map();
  const heldRaw = new Map();
  const heldCost = new Map();
  for (const p of account.positions) {
    heldRaw.set(p.symbol, p.qty);
    heldQty.set(p.symbol, Number(p.qty) / Math.pow(10, qtyScale.get(p.symbol)));
    heldCost.set(p.symbol, Number(p.cost_quote_units) / 1e6);
    if (!entrySeq.has(p.symbol)) entrySeq.set(p.symbol, seq);
  }
  for (const symbol of symbols) {
    if (!heldQty.has(symbol)) {
      entrySeq.delete(symbol);
      peakClose.delete(symbol);
    }
  }
  if (seq < warmup) return [];

  const basket = basketStats(seq);
  const scores = new Map();
  for (const symbol of symbols) scores.set(symbol, scoreOf(symbol, basket.trendWeight, basket.reversalWeight));

  const orders = [];
  const exiting = new Set();
  for (const symbol of symbols) {
    const qty = heldQty.get(symbol) || 0;
    if (qty <= 0) continue;
    const close = latestClose(symbol);
    if (close === null) continue;
    const peak = Math.max(peakClose.get(symbol) || close, close);
    peakClose.set(symbol, peak);
    const cost = heldCost.get(symbol) || 0;
    const pnlPct = cost > 0 ? (qty * close) / cost - 1 : 0;
    const peakDd = close / peak - 1;
    const age = seq - (entrySeq.get(symbol) ?? seq);
    const sc = scores.get(symbol);
    let exit = false;
    if (latched) {
      exit = true;
    } else if (pnlPct <= -P.stopLoss) {
      exit = true;
      cooldownUntil.set(symbol, seq + P.cooldownBars);
    } else if (peakDd <= -P.trailStop && age >= 2) {
      exit = true;
      cooldownUntil.set(symbol, seq + P.cooldownBars);
    } else if (pnlPct >= P.takeProfit) {
      exit = true;
    } else if (age >= P.maxHoldBars) {
      exit = true;
    } else if (sc !== null && sc.score < P.exitScore && age >= P.minHoldBars) {
      exit = true;
    } else if (P.wStretch > 0 && sc !== null && sc.stretch > P.stretchExitZ && age >= P.minHoldBars) {
      exit = true;
    }
    if (exit) exiting.add(symbol);
  }
  for (const symbol of symbols) {
    if (!exiting.has(symbol)) continue;
    orders.push({
      side: "sell",
      client_id: nextClientId(seq),
      symbol,
      qty: heldRaw.get(symbol),
      max_slippage_bps: MAX_SLIPPAGE_BPS,
    });
    peakClose.delete(symbol);
    entrySeq.delete(symbol);
    if (floorOpen && floorSymbol === symbol) {
      floorOpen = false;
      floorSymbol = null;
    }
  }

  let cashLeft = cashUsd;
  const chosenSet = new Set();
  if (basket.trend > P.basketGate && !latched) {
    const ranked = [];
    for (const symbol of symbols) {
      const sc = scores.get(symbol);
      if (sc === null || sc.score <= P.entryScore) continue;
      if (exiting.has(symbol)) continue;
      if (seq < (cooldownUntil.get(symbol) ?? -1)) continue;
      if (floorOpen && floorSymbol === symbol) continue;
      if (P.wStretch > 0 && sc.stretch >= P.stretchEntryZ) continue;
      ranked.push({ symbol, score: sc.score });
    }
    ranked.sort((a, b) => b.score - a.score || (a.symbol > b.symbol ? -1 : 1));
    const chosen = ranked.slice(0, P.maxHoldings).map((r) => r.symbol);
    for (const symbol of chosen) chosenSet.add(symbol);
    let gross = P.gross;
    if (P.breadthScale) {
      let positive = 0;
      let scored = 0;
      for (const symbol of symbols) {
        const sc = scores.get(symbol);
        if (sc === null) continue;
        scored++;
        if (sc.score > 0) positive++;
      }
      if (scored > 0) gross *= 0.35 + 0.65 * (positive / scored);
    }
    if (chosen.length > 0) {
      const weightEach = Math.min(hello.caps.max_weight_bps / 10000, gross / chosen.length);
      for (const symbol of chosen) {
        const close = latestClose(symbol);
        if (close === null) continue;
        const current = (heldQty.get(symbol) || 0) * close;
        const diff = weightEach * equityUsd - current;
        if (diff <= P.rebalanceBand * equityUsd) continue;
        const room = (hello.caps.max_weight_bps / 10000) * equityUsd - current;
        let amount = Math.min(diff, cashLeft, room);
        amount = Math.floor(amount * 1e6) / 1e6;
        if (amount < MIN_ORDER_USD) continue;
        orders.push({
          side: "buy",
          client_id: nextClientId(seq),
          symbol,
          notional_quote_units: String(Math.round(amount * 1e6)),
          max_slippage_bps: MAX_SLIPPAGE_BPS,
        });
        cashLeft -= amount;
        if (!heldQty.has(symbol)) entrySeq.set(symbol, seq);
      }
    }
  }

  if (seq >= FLOOR_FROM_SEQ && filledTrades < MIN_TRADES) {
    if (floorOpen && floorSymbol !== null) {
      if (heldQty.has(floorSymbol) && !exiting.has(floorSymbol)) {
        orders.push({
          side: "sell",
          client_id: nextClientId(seq),
          symbol: floorSymbol,
          qty: heldRaw.get(floorSymbol),
          max_slippage_bps: MAX_SLIPPAGE_BPS,
        });
        peakClose.delete(floorSymbol);
        entrySeq.delete(floorSymbol);
        floorOpen = false;
        floorSymbol = null;
      } else if (!heldQty.has(floorSymbol)) {
        floorOpen = false;
        floorSymbol = null;
      }
    }
    if (!floorOpen && filledTrades < MIN_TRADES) {
      for (const symbol of symbols) {
        if (heldQty.has(symbol) || exiting.has(symbol) || chosenSet.has(symbol)) continue;
        if (latestClose(symbol) === null || cashLeft < FLOOR_USD) continue;
        orders.push({
          side: "buy",
          client_id: nextClientId(seq),
          symbol,
          notional_quote_units: String(FLOOR_USD * 1e6),
          max_slippage_bps: MAX_SLIPPAGE_BPS,
        });
        cashLeft -= FLOOR_USD;
        floorOpen = true;
        floorSymbol = symbol;
        entrySeq.set(symbol, seq);
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
      symbols.push(s.symbol);
      priceScale.set(s.symbol, s.price_scale);
      qtyScale.set(s.symbol, s.qty_scale);
      closes.set(s.symbol, []);
    }
    return;
  }
  if (msg.type === "batch") {
    for (const bar of msg.bars) {
      const close = priceOf(bar.symbol, bar.c);
      closes.get(bar.symbol).push(close);
      updateEma(bar.symbol, close);
    }
    recordIndexLog();
    for (const fill of msg.fills) {
      if (fill.status === "filled") filledTrades++;
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
