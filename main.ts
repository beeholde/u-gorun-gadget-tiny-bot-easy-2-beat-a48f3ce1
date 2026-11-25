// Tiny hourly bars bot for agent-fun/bars-replay/v1.
//
// Each batch the bot scores every symbol with a volatility-normalized blend of
// EMA trend and multi-hour momentum, optionally discounted by how stretched
// price is above its slow EMA. It holds the strongest few names while a
// basket-trend gate is open, leaves on stop, trailing, take-profit or score
// exits, and otherwise sits in cash. A small activity floor keeps the filled
// trade count at the guardrail minimum when the market offers nothing.
//
// The bot reads the hello and batches on stdin and answers each batch with one
// reply line of orders for the next bar open. It keeps no state outside the
// run, uses no clock and no randomness, and sizes every order from the
// account the batch itself carries.

const MAX_SLIPPAGE_BPS = 500;
const MIN_ORDER_USD = 25;
const FLOOR_USD = 100;
const FLOOR_FROM_SEQ = 20;
const MIN_TRADES = 8;

const P = {
  fast: 6,
  slow: 18,
  momLookback: 12,
  volWindow: 24,
  wTrend: 1.0,
  wMom: 0.5,
  wStretch: 0.0,
  stretchEntryZ: 9.0,
  stretchExitZ: 9.0,
  entryScore: 0.6,
  exitScore: 0.0,
  maxHoldings: 4,
  gross: 1.0,
  breadthScale: true,
  basketLookback: 24,
  basketGate: -1.0,
  stopLoss: 0.06,
  trailStop: 0.05,
  takeProfit: 9.0,
  cooldownBars: 6,
  minBars: 8,
  minHoldBars: 0,
  rebalanceBand: 0.03,
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

function scoreOf(symbol) {
  const list = closes.get(symbol);
  const n = list.length;
  if (n < P.minBars) return null;
  const vol = volatility(symbol);
  const slow = emaSlow.get(symbol);
  const trend = (emaFast.get(symbol) - slow) / slow;
  const look = Math.min(P.momLookback, n - 1);
  const mom = look >= 2 ? (list[n - 1] / list[n - 1 - look] - 1) / Math.sqrt(look) : 0;
  const stretch = Math.log(list[n - 1] / slow) / (vol * Math.sqrt(P.slow / 2));
  return {
    score: (P.wTrend * trend + P.wMom * mom) / vol - P.wStretch * stretch,
    stretch,
  };
}

function basketTrend() {
  let now = 0;
  let back = 0;
  let count = 0;
  for (const symbol of symbols) {
    const list = closes.get(symbol);
    if (!list || list.length < 5) continue;
    const lag = Math.min(P.basketLookback, list.length - 1);
    now += list[list.length - 1] / list[0];
    back += list[list.length - 1 - lag] / list[0];
    count++;
  }
  if (count === 0 || back <= 0) return 0;
  return now / back - 1;
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

  const scores = new Map();
  for (const symbol of symbols) scores.set(symbol, scoreOf(symbol));

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
    if (pnlPct <= -P.stopLoss) {
      exit = true;
      cooldownUntil.set(symbol, seq + P.cooldownBars);
    } else if (peakDd <= -P.trailStop && age >= 2) {
      exit = true;
      cooldownUntil.set(symbol, seq + P.cooldownBars);
    } else if (pnlPct >= P.takeProfit) {
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
  }

  if (basketTrend() > P.basketGate) {
    const ranked = [];
    for (const symbol of symbols) {
      const sc = scores.get(symbol);
      if (sc === null || sc.score <= P.entryScore) continue;
      if (exiting.has(symbol)) continue;
      if (seq < (cooldownUntil.get(symbol) ?? -1)) continue;
      if (P.wStretch > 0 && sc.stretch >= P.stretchEntryZ) continue;
      ranked.push({ symbol, score: sc.score });
    }
    ranked.sort((a, b) => b.score - a.score || (a.symbol < b.symbol ? -1 : 1));
    const chosen = ranked.slice(0, P.maxHoldings).map((r) => r.symbol);
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
      let cashLeft = cashUsd;
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

  if (seq >= FLOOR_FROM_SEQ && filledTrades < MIN_TRADES && orders.length === 0) {
    const floorSymbol = symbols.includes("SOL") ? "SOL" : symbols[0];
    if (floorSymbol && latestClose(floorSymbol) !== null) {
      if (floorOpen && heldQty.has(floorSymbol)) {
        orders.push({
          side: "sell",
          client_id: nextClientId(seq),
          symbol: floorSymbol,
          qty: heldRaw.get(floorSymbol),
          max_slippage_bps: MAX_SLIPPAGE_BPS,
        });
        floorOpen = false;
      } else if (!heldQty.has(floorSymbol) && cashUsd >= FLOOR_USD) {
        orders.push({
          side: "buy",
          client_id: nextClientId(seq),
          symbol: floorSymbol,
          notional_quote_units: String(FLOOR_USD * 1e6),
          max_slippage_bps: MAX_SLIPPAGE_BPS,
        });
        floorOpen = true;
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
