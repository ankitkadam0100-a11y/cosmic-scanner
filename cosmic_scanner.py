#!/usr/bin/env python3
"""
Cosmic BTC options scanner  -  ALERT ONLY (places no orders, needs no API key).

What it does
  * Lists every active BTC option on Cosmic (all expiries) and keeps the list fresh.
  * Streams their mark prices from the public WebSocket (wss://cosmic.trade/feeds).
  * Builds 15-minute candles, converts them to Heikin Ashi, and computes
    Supertrend(10, 3), EMA 20 and EMA 50 on the Heikin Ashi candles.
  * It alerts ONCE per option, at the moment the setup STARTS: the candle that closes with
    BOTH conditions true, right after a candle where they were not both true.
    Options already in the setup when the scanner starts stay silent, and so do all later
    candles while the setup continues. A new alert needs the setup to end and start again.

SETUP (on the just-closed 15m Heikin Ashi candle)
  1. Supertrend(10, 3) is bearish (HA close below the Supertrend line)
  2. EMA 50 > EMA 20

FILTERS (a signal that fails one is NOT sent to you, but is still written to signals.csv with the reason)
  mark price >= 30 | spread <= 20% | at least 4 hours to expiry |
  not a "late signal" (HA close not already more than 50% below EMA 50)

Setup
  pip install aiohttp websockets msgpack
  # optional Telegram alerts:
  export TELEGRAM_BOT_TOKEN="123456:ABC..."
  export TELEGRAM_CHAT_ID="123456789"          # several people: "123456789,987654321"
  python cosmic_scanner.py
"""
import asyncio
import csv
import io
import json
import logging
import os
import time
from collections import deque
from datetime import datetime, timedelta, timezone

import aiohttp
import msgpack
import websockets

try:                                   # charts are optional: without matplotlib alerts are text only
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import Rectangle
    HAVE_MPL = True
except Exception:
    HAVE_MPL = False

# ============================== CONFIG ==============================
BASE_URL = os.getenv("COSMIC_BASE", "https://cosmic.trade")
WS_URL = BASE_URL.replace("https://", "wss://").replace("http://", "ws://") + "/feeds"

UNDERLYING = "BTC"                 # only options on this underlying ("" = all)
CANDLE_SECONDS = int(os.getenv("CANDLE_SECONDS", "900"))   # 15 minutes
ST_PERIOD, ST_MULT = 10, 3.0       # Supertrend(10, 3)
EMA_FAST, EMA_SLOW = 20, 50
MIN_CANDLES = int(os.getenv("MIN_CANDLES", "60"))          # warm-up before signals count
MAX_CANDLES = 400

# Alert filters (signals that fail are still written to signals.csv, marked not alerted)
MIN_MARK_PRICE = float(os.getenv("MIN_MARK_PRICE", "30"))                  # mark price (as shown in the alert) at least this
MAX_SPREAD_PCT = 20.0                                                      # (ask-bid)/mid must not be wider than this
MIN_MINUTES_TO_EXPIRY = float(os.getenv("MIN_MINUTES_TO_EXPIRY", "240"))   # at least 4 hours to expiry
MAX_BELOW_EMA50_PCT = float(os.getenv("MAX_BELOW_EMA50_PCT", "50"))        # "late signal": price already this far below EMA50
COVERAGE_CSV = os.getenv("COVERAGE_CSV", "coverage.csv")                   # which candle closes the scanner watched

# Connection handling (Cosmic does not document a per-connection symbol limit)
MAX_SYMBOLS_PER_CONN = 150
SUBSCRIBE_BATCH = 50
CONTRACT_REFRESH_SECS = 300
BACKFILL = os.getenv("BACKFILL", "1") == "1"   # try /mark-klines so signals start sooner
BACKFILL_CONCURRENCY = 4
CLOSE_GRACE_SECS = 2               # wait this long after a candle ends for late ticks
MAX_ALERT_LINES = 25

TELEGRAM_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT = os.getenv("TELEGRAM_CHAT_ID")      # one id, or several separated by commas: 111,222
TELEGRAM_CHATS = [c.strip() for c in (TELEGRAM_CHAT or "").split(",") if c.strip()]
SIGNAL_CSV = os.getenv("SIGNAL_CSV", "signals.csv")
CHARTS = os.getenv("CHARTS", "1") == "1"       # send a chart image with each alert
CHART_CANDLES = 80                             # candles shown on the chart (~20 hours)
MAX_CHARTS_PER_BATCH = 5                       # at most this many charts per candle close
CHART_DIR = "charts"                           # PNGs are also saved here
# =====================================================================

log = logging.getLogger("scanner")
IST = timezone(timedelta(hours=5, minutes=30))


# ------------------------- indicators --------------------------------
def ema_series(vals, n):
    out = [None] * len(vals)
    if len(vals) < n:
        return out
    k = 2.0 / (n + 1)
    e = sum(vals[:n]) / n
    out[n - 1] = e
    for i in range(n, len(vals)):
        e = vals[i] * k + e * (1 - k)
        out[i] = e
    return out


def compute_series(candles):
    """candles: list of (bucket, o, h, l, c). Returns per-candle lists (None where not defined yet)
    for Heikin Ashi, Supertrend and EMAs, all computed on the Heikin Ashi candles."""
    n = len(candles)
    o = [x[1] for x in candles]
    h = [x[2] for x in candles]
    l = [x[3] for x in candles]
    c = [x[4] for x in candles]

    # Heikin Ashi
    hac = [(o[i] + h[i] + l[i] + c[i]) / 4.0 for i in range(n)]
    hao = [0.0] * n
    hao[0] = (o[0] + c[0]) / 2.0
    for i in range(1, n):
        hao[i] = (hao[i - 1] + hac[i - 1]) / 2.0
    hah = [max(h[i], hao[i], hac[i]) for i in range(n)]
    hal = [min(l[i], hao[i], hac[i]) for i in range(n)]

    # ATR (Wilder / RMA) on HA candles
    tr = [hah[0] - hal[0]] + [
        max(hah[i] - hal[i], abs(hah[i] - hac[i - 1]), abs(hal[i] - hac[i - 1]))
        for i in range(1, n)
    ]
    P = ST_PERIOD
    atr = [None] * n
    atr[P - 1] = sum(tr[:P]) / P
    for i in range(P, n):
        atr[i] = (atr[i - 1] * (P - 1) + tr[i]) / P

    # Supertrend (direction: 1 = bullish, -1 = bearish)
    st_list, dir_list = [None] * n, [None] * n
    fub = flb = None
    d = 1
    for i in range(P - 1, n):
        hl2 = (hah[i] + hal[i]) / 2.0
        ub = hl2 + ST_MULT * atr[i]
        lb = hl2 - ST_MULT * atr[i]
        if i == P - 1:
            fub, flb = ub, lb
            d = 1 if hac[i] > hl2 else -1
        else:
            fub = ub if (ub < fub or hac[i - 1] > fub) else fub
            flb = lb if (lb > flb or hac[i - 1] < flb) else flb
            if d == 1:
                d = -1 if hac[i] < flb else 1
            else:
                d = 1 if hac[i] > fub else -1
        st_list[i] = flb if d == 1 else fub
        dir_list[i] = d

    return {"ha_open": hao, "ha_high": hah, "ha_low": hal, "ha_close": hac,
            "st": st_list, "dir": dir_list,
            "ema_fast": ema_series(hac, EMA_FAST), "ema_slow": ema_series(hac, EMA_SLOW)}


def analyze(candles):
    """Indicator values for the LAST candle (Heikin Ashi). None if there is not enough data."""
    if len(candles) < max(EMA_SLOW, ST_PERIOD + 1):
        return None
    s = compute_series(candles)
    return {k: s[k][-1] for k in ("ha_open", "ha_high", "ha_low", "ha_close", "st", "dir",
                                  "ema_fast", "ema_slow")}


def render_chart(sig):
    """Draws the option's Heikin Ashi chart with Supertrend, EMA20, EMA50 and the signal candle.
    Returns PNG bytes. Runs in a worker thread."""
    sym, candles = sig["sym"], sig["candles"]
    s = compute_series(candles)
    n = len(candles)
    start = max(0, n - CHART_CANDLES)
    idx = list(range(start, n))
    nan = float("nan")
    val = lambda key: [s[key][i] if s[key][i] is not None else nan for i in idx]
    bg, fg, grid = "#131316", "#d1d4dc", "#2a2e39"

    fig, ax = plt.subplots(figsize=(10, 5.6), dpi=110)
    fig.patch.set_facecolor(bg)
    ax.set_facecolor(bg)
    ys = []
    for i in idx:
        o_, h_, l_, c_ = s["ha_open"][i], s["ha_high"][i], s["ha_low"][i], s["ha_close"][i]
        col = "#26a69a" if c_ >= o_ else "#ef5350"
        ax.plot([i, i], [l_, h_], color=col, lw=1, zorder=3)
        ax.add_patch(Rectangle((i - 0.3, min(o_, c_)), 0.6, max(abs(c_ - o_), 1e-9), color=col, zorder=3))
        ys += [l_, h_]
    # Supertrend: one line per same-direction run (green = bullish, red = bearish)
    run = []

    def flush():
        if len(run) >= 1:
            col = "#1e9e52" if run[0][1] == 1 else "#c0392b"
            ax.plot([r[0] for r in run], [r[2] for r in run], color=col, lw=2.2, zorder=2,
                    marker="o" if len(run) == 1 else None, markersize=5)
        run.clear()
    for i in idx:
        d_ = s["dir"][i]
        if d_ is None:
            flush()
            continue
        if run and run[-1][1] != d_:
            flush()
        run.append((i, d_, s["st"][i]))
        ys.append(s["st"][i])
    flush()
    ef, es = val("ema_fast"), val("ema_slow")
    ax.plot(idx, ef, color="#7bd88f", lw=1.2, zorder=4)
    ax.plot(idx, es, color="#ff6b6b", lw=1.2, zorder=4)
    ys += [v for v in ef + es if v == v]

    last = n - 1
    ax.axvline(last, ls="--", color="#787b86", lw=0.8, zorder=1)
    ax.annotate("SIGNAL", xy=(last, s["ha_high"][last]), xytext=(-55, 28), textcoords="offset points",
                color="#f0b90b", fontsize=9, fontweight="bold",
                arrowprops=dict(arrowstyle="->", color="#f0b90b"))
    lo, hi = min(ys), max(ys)
    pad = (hi - lo) * 0.06 or 1.0
    ax.set_ylim(lo - pad, hi + pad)
    ax.set_xlim(start - 1, last + 3)

    ticks = list(range(start, n, 8))
    labels, prev_day = [], None
    for t in ticks:
        dt = datetime.fromtimestamp(candles[t][0] * CANDLE_SECONDS, IST)
        labels.append(dt.strftime("%d %b\n%H:%M") if dt.date() != prev_day else dt.strftime("%H:%M"))
        prev_day = dt.date()
    ax.set_xticks(ticks)
    ax.set_xticklabels(labels, color=fg, fontsize=8)
    ax.yaxis.tick_right()
    ax.tick_params(axis="y", colors=fg, labelsize=8)
    ax.grid(color=grid, lw=0.5, zorder=0)
    for sp in ax.spines.values():
        sp.set_color(grid)
    from matplotlib.lines import Line2D
    r = sig["r"]
    ax.legend(handles=[
        Line2D([0], [0], color="#c0392b", lw=2.2, label=f"Supertrend({ST_PERIOD},{ST_MULT:g})  {r['st']:.1f}"),
        Line2D([0], [0], color="#7bd88f", lw=1.2, label=f"EMA{EMA_FAST}  {r['ema_fast']:.1f}"),
        Line2D([0], [0], color="#ff6b6b", lw=1.2, label=f"EMA{EMA_SLOW}  {r['ema_slow']:.1f}")],
        loc="best", fontsize=8, facecolor=bg, edgecolor=grid, labelcolor=fg, framealpha=0.7)
    ax.set_title(f"{sym.name}  |  {CANDLE_SECONDS / 60:g}m Heikin Ashi (mark price)  |  signal candle closed "
                 f"{sig['candle']} IST", color=fg, fontsize=10, loc="left")
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", facecolor=bg)
    plt.close(fig)
    return buf.getvalue()


def is_bearish(r):
    if r is None or r["ema_fast"] is None or r["ema_slow"] is None:
        return False
    # tiny tolerance so a perfectly flat price can never count as "EMA50 > EMA20"
    ema_ok = (r["ema_slow"] - r["ema_fast"]) > 1e-6 * max(1.0, abs(r["ema_slow"]))
    return r["dir"] == -1 and ema_ok


def filter_reason(mark, spread, mins_left, r):
    """Returns "" if a signal should be alerted, otherwise the reason it is skipped."""
    if mark < MIN_MARK_PRICE:
        return "price too low"
    if spread is not None and spread > MAX_SPREAD_PCT:
        return "spread too wide"
    if mins_left < MIN_MINUTES_TO_EXPIRY:
        return "expires too soon"
    if r["ema_slow"] > 0 and (r["ema_slow"] - r["ha_close"]) / r["ema_slow"] * 100 > MAX_BELOW_EMA50_PCT:
        return "late signal"
    return ""


# ------------------------- state --------------------------------------
class Sym:
    def __init__(self, name, kind, strike, expiry):
        self.name, self.kind, self.strike, self.expiry = name, kind, strike, expiry
        self.candles = deque(maxlen=MAX_CANDLES)   # closed: (bucket, o, h, l, c)
        self.cur = None                            # [o, h, l, c] of the open candle
        self.cur_bucket = None
        self.price = None
        self.bid = None
        self.ask = None
        self.ticks = 0
        self.prev_bearish = None                   # None = not evaluated yet


states = {}          # option symbol -> Sym
rt = {"rebuilding": False, "gap": False}     # set when the scanner was paused (sleep / lost connection)
bg_tasks = set()
workers = []
pending = []         # signals waiting to be flushed
btc = {"price": None}
stats = {"msgs": 0, "start": time.time()}


def advance(sym, to_bucket):
    """Close the open candle(s) up to (not including) to_bucket. True if any closed."""
    if sym.cur is None or to_bucket <= sym.cur_bucket:
        return False
    o, h, l, c = sym.cur
    sym.candles.append((sym.cur_bucket, o, h, l, c))
    for k in range(min(to_bucket - sym.cur_bucket - 1, 200)):      # flat candles for gaps
        sym.candles.append((sym.cur_bucket + 1 + k, c, c, c, c))
    sym.cur_bucket = to_bucket
    sym.cur = [c, c, c, c]
    return True


def on_tick(sym, price, now):
    if rt["rebuilding"]:
        return
    b = int(now // CANDLE_SECONDS)
    if sym.cur is not None and b - sym.cur_bucket > 2:      # we were paused: history is unreliable
        rt["gap"] = True
        return
    closed = False
    if sym.cur is None:
        if sym.candles:                                            # continue after backfill
            last_b, _, _, _, last_c = sym.candles[-1]
            for k in range(min(b - last_b - 1, 200)):
                sym.candles.append((last_b + 1 + k, last_c, last_c, last_c, last_c))
        sym.cur_bucket, sym.cur = b, [price, price, price, price]
    else:
        closed = advance(sym, b)
        sym.cur[1] = max(sym.cur[1], price)
        sym.cur[2] = min(sym.cur[2], price)
        sym.cur[3] = price
    sym.price = price
    sym.ticks += 1
    if closed:
        evaluate(sym, now)


def evaluate(sym, now):
    if len(sym.candles) < MIN_CANDLES:
        return
    r = analyze(list(sym.candles))
    bear = is_bearish(r)
    prev, sym.prev_bearish = sym.prev_bearish, bear
    if not (bear and prev is False):          # alert only on a fresh flip to all-bearish
        return
    mark = r["ha_close"] if sym.price is None else sym.price
    spread = None
    if sym.bid and sym.ask and sym.bid > 0 and sym.ask > 0:
        spread = (sym.ask - sym.bid) / ((sym.ask + sym.bid) / 2) * 100
    mins_left = (sym.expiry - now) / 60
    reason = filter_reason(mark, spread, mins_left, r)
    ct = datetime.fromtimestamp((sym.candles[-1][0] + 1) * CANDLE_SECONDS, IST).strftime("%d %b %H:%M")
    sig = {"time": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S"), "sym": sym, "mark": mark, "candle": ct,
           "spread": spread, "mins_left": mins_left, "r": r, "alerted": reason == "", "reason": reason}
    write_csv(sig)
    if sig["alerted"]:
        sig["candles"] = list(sym.candles)          # for the chart
        pending.append(sig)


def write_csv(s):
    new = not os.path.exists(SIGNAL_CSV)
    sym, r = s["sym"], s["r"]
    with open(SIGNAL_CSV, "a", newline="") as f:
        w = csv.writer(f)
        if new:
            w.writerow(["time_utc", "symbol", "type", "strike", "btc", "mark", "bid", "ask",
                        "spread_pct", "mins_to_expiry", "ha_close", "supertrend", "ema20", "ema50",
                        "alerted", "reason"])
        w.writerow([s["time"], sym.name, sym.kind, sym.strike, btc["price"], round(s["mark"], 2), sym.bid, sym.ask,
                    None if s["spread"] is None else round(s["spread"], 2), round(s["mins_left"]),
                    round(r["ha_close"], 2), round(r["st"], 2), round(r["ema_fast"], 2),
                    round(r["ema_slow"], 2), s["alerted"], s["reason"]])


def fmt_line(s):
    sym = s["sym"]
    dist = ""
    if btc["price"]:
        dist = f" | strike {sym.strike:g} ({(sym.strike / btc['price'] - 1) * 100:+.1f}% vs BTC)"
    sp = "n/a" if s["spread"] is None else f"{s['spread']:.1f}%"
    h, m = divmod(int(s["mins_left"]), 60)
    r = s["r"]
    return (f"{sym.name} | mark {s['mark']:.1f} | spread {sp}{dist} | exp in {h}h{m:02d}m"
            f" | ST {r['st']:.1f} EMA20 {r['ema_fast']:.1f} < EMA50 {r['ema_slow']:.1f}")


async def notify(http, text):
    print(text, flush=True)
    if TELEGRAM_TOKEN and TELEGRAM_CHATS:
        for chat in TELEGRAM_CHATS:                # one failing chat never blocks the others
            try:
                async with http.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                                     json={"chat_id": chat, "text": text[:4000]},
                                     timeout=aiohttp.ClientTimeout(total=15)) as resp:
                    if resp.status != 200:
                        log.warning("Telegram error for chat %s: %s %s", chat, resp.status, (await resp.text())[:200])
            except Exception as e:
                log.warning("Telegram send failed for chat %s: %r", chat, e)


async def send_photo(http, png, caption):
    if not (TELEGRAM_TOKEN and TELEGRAM_CHATS):
        return
    for chat in TELEGRAM_CHATS:
        try:
            form = aiohttp.FormData()
            form.add_field("chat_id", chat)
            form.add_field("caption", caption[:1000])
            form.add_field("photo", png, filename="chart.png", content_type="image/png")
            async with http.post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendPhoto", data=form,
                                 timeout=aiohttp.ClientTimeout(total=30)) as resp:
                if resp.status != 200:
                    log.warning("Telegram photo error for chat %s: %s %s", chat, resp.status, (await resp.text())[:200])
        except Exception as e:
            log.warning("Telegram photo failed for chat %s: %r", chat, e)


# ------------------------- websocket ----------------------------------
def handle_frame(msg):
    if isinstance(msg, str):
        return
    try:
        data = msgpack.unpackb(msg, raw=False)
    except Exception:
        return
    for d in (data if isinstance(data, list) else [data]):
        if not isinstance(d, dict):
            continue
        stats["msgs"] += 1
        name = d.get("s")
        price = d.get("mp") or d.get("lp")
        try:
            price = float(price) if price is not None else None
        except (TypeError, ValueError):
            price = None
        if name == UNDERLYING + "USDT":
            if price:
                btc["price"] = price
            continue
        sym = states.get(name)
        if sym is None:
            continue
        try:
            if d.get("bp") is not None:
                sym.bid = float(d["bp"])
            if d.get("ap") is not None:
                sym.ask = float(d["ap"])
        except (TypeError, ValueError):
            pass
        if price and price > 0:
            on_tick(sym, price, time.time())


class Worker:
    def __init__(self, idx):
        self.idx, self.symbols, self.ws = idx, set(), None

    async def _send(self, action, syms):
        syms = list(syms)
        for i in range(0, len(syms), SUBSCRIBE_BATCH):
            await self.ws.send(json.dumps({"action": action, "symbols": syms[i:i + SUBSCRIBE_BATCH]}))
            await asyncio.sleep(0.05)

    async def add(self, syms):
        self.symbols |= set(syms)
        if self.ws:
            try:
                await self._send("subscribe", syms)
            except Exception:
                pass                       # re-subscribed in full on reconnect

    async def remove(self, syms):
        self.symbols -= set(syms)
        if self.ws and syms:
            try:
                await self._send("unsubscribe", syms)
            except Exception:
                pass

    async def run(self):
        backoff = 1
        while True:
            try:
                async with websockets.connect(WS_URL, ping_interval=15, ping_timeout=20, max_size=None) as ws:
                    self.ws, backoff = ws, 1
                    log.info("worker %d connected (%d symbols)", self.idx, len(self.symbols))
                    await self._send("subscribe", self.symbols)
                    async for msg in ws:
                        handle_frame(msg)
            except Exception as e:
                log.warning("worker %d disconnected: %r", self.idx, e)
            self.ws = None
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, 60)


async def assign(names):
    buckets = {}
    for s in names:
        w = next((w for w in workers if len(w.symbols) + len(buckets.get(w, [])) < MAX_SYMBOLS_PER_CONN), None)
        if w is None:
            w = Worker(len(workers))
            workers.append(w)
            asyncio.create_task(w.run())
        buckets.setdefault(w, []).append(s)
    for w, lst in buckets.items():
        await w.add(lst)


# ------------------------- contracts / backfill -----------------------
async def fetch_contracts(http):
    async with http.get(f"{BASE_URL}/api/v1/contracts", timeout=aiohttp.ClientTimeout(total=30)) as resp:
        resp.raise_for_status()
        arr = await resp.json()
    out, now = {}, time.time()
    for c in arr:
        if c.get("instrument_kind") not in ("option_call", "option_put"):
            continue
        if UNDERLYING and c.get("underlying_symbol") != UNDERLYING:
            continue
        if not c.get("is_active") or c.get("status") != "Trading":
            continue
        try:
            exp = datetime.fromisoformat(c["expiry_ts"].replace("Z", "+00:00")).timestamp()
            strike = float(c["strike_price"])
        except Exception:
            continue
        if exp > now:
            out[c["symbol"]] = ("CALL" if c["instrument_kind"] == "option_call" else "PUT", strike, exp)
    return out


async def backfill_one(http, sem, sym):
    interval = str(max(1, CANDLE_SECONDS // 60))
    now = int(time.time())
    cur_b = now // CANDLE_SECONDS
    url = (f"{BASE_URL}/api/v1/charts/{sym.name}/mark-klines?interval={interval}"
           f"&from={now - 300 * CANDLE_SECONDS}&to={now + CANDLE_SECONDS}")
    async with sem:
        try:
            async with http.get(url, timeout=aiohttp.ClientTimeout(total=20)) as resp:
                if resp.status == 429:
                    await asyncio.sleep(float(resp.headers.get("Retry-After", "2")))
                    return False
                if resp.status != 200:
                    return False
                bars = await resp.json()
        except Exception:
            return False
        await asyncio.sleep(0.05)
    ok = False
    for b in bars if isinstance(bars, list) else []:
        try:
            bucket = int(b["time"]) // CANDLE_SECONDS
            o_, h_, l_, c_ = float(b["open"]), float(b["high"]), float(b["low"]), float(b["close"])
            if bucket == cur_b:            # still-open bar: continue it with live ticks
                sym.cur_bucket, sym.cur = cur_b, [o_, h_, l_, c_]
                continue
            if bucket > cur_b:
                continue
            sym.candles.append((bucket, o_, h_, l_, c_))
            ok = True
        except Exception:
            continue
    return ok


async def contracts_loop(http):
    first = True
    while True:
        try:
            wanted = await fetch_contracts(http)
            new = [s for s in wanted if s not in states]
            gone = [s for s in states if s not in wanted]
            for s in new:
                kind, strike, exp = wanted[s]
                states[s] = Sym(s, kind, strike, exp)
            if new and BACKFILL:
                sem = asyncio.Semaphore(BACKFILL_CONCURRENCY)
                res = await asyncio.gather(*(backfill_one(http, sem, states[s]) for s in new))
                log.info("backfill: %d/%d options returned mark-kline history", sum(res), len(new))
                for s in new:                  # current state from history -> only NEW starts alert
                    st_ = states[s]
                    if len(st_.candles) >= MIN_CANDLES:
                        st_.prev_bearish = is_bearish(analyze(list(st_.candles)))
            if first:
                await assign([UNDERLYING + "USDT"])
                first = False
            if new:
                await assign(new)
            for w in workers:
                await w.remove([s for s in gone if s in w.symbols])
            for s in gone:
                states.pop(s, None)
            if new or gone:
                log.info("tracking %d options (+%d new, -%d expired)", len(states), len(new), len(gone))
        except Exception as e:
            log.warning("contract refresh failed: %r", e)
        await asyncio.sleep(CONTRACT_REFRESH_SECS)


# ------------------------- loops --------------------------------------
def write_coverage(bucket):
    """Records that the scanner watched the close of this candle (used by audit_signals.py)."""
    ready = sum(1 for x in states.values() if len(x.candles) >= MIN_CANDLES)
    new = not os.path.exists(COVERAGE_CSV)
    with open(COVERAGE_CSV, "a", newline="") as f:
        w = csv.writer(f)
        if new:
            w.writerow(["bucket", "close_time_utc", "options_checked"])
        w.writerow([bucket, datetime.fromtimestamp((bucket + 1) * CANDLE_SECONDS, timezone.utc)
                    .strftime("%Y-%m-%d %H:%M:%S"), ready])


async def rebuild_all(http):
    """After a pause (computer sleep / lost connection) the candle history is unreliable: reload it."""
    rt["rebuilding"] = True
    try:
        syms = list(states.values())
        for x in syms:
            x.candles.clear()
            x.cur, x.cur_bucket = None, None
        sem = asyncio.Semaphore(BACKFILL_CONCURRENCY)
        res = await asyncio.gather(*(backfill_one(http, sem, x) for x in syms))
        for x in syms:
            x.prev_bearish = is_bearish(analyze(list(x.candles))) if len(x.candles) >= MIN_CANDLES else None
        log.info("history rebuilt: %d/%d options", sum(res), len(syms))
    finally:
        rt["rebuilding"], rt["gap"] = False, False


async def flush_alerts(http, batch):
    batch.sort(key=lambda x: (x["sym"].expiry, x["sym"].kind, x["sym"].strike))
    lines = [fmt_line(x) for x in batch[:MAX_ALERT_LINES]]
    if len(batch) > MAX_ALERT_LINES:
        lines.append(f"... +{len(batch) - MAX_ALERT_LINES} more (see {SIGNAL_CSV})")
    head = (f"NEW SETUP: Supertrend({ST_PERIOD},{ST_MULT:g}) bearish + EMA50>EMA20 | "
            f"{CANDLE_SECONDS / 60:g}m HA candle closed {batch[0]['candle']} IST | {len(batch)} option(s)")
    await notify(http, head + "\n" + "\n".join(lines))
    if CHARTS and HAVE_MPL:
        for x in batch[:MAX_CHARTS_PER_BATCH]:
            try:
                png = await asyncio.to_thread(render_chart, x)
                os.makedirs(CHART_DIR, exist_ok=True)
                fn = os.path.join(CHART_DIR, f"{x['sym'].name}_{x['candle'].replace(' ', '').replace(':', '')}.png")
                with open(fn, "wb") as f:
                    f.write(png)
                log.info("chart saved: %s", fn)
                await send_photo(http, png, fmt_line(x))
            except Exception as e:
                log.warning("chart failed for %s: %r", x["sym"].name, e)


async def roll_loop(http):
    """Closes candles for options that had no ticks, records coverage, and sends grouped alerts."""
    last_b = None
    while True:
        await asyncio.sleep(1)
        if rt["rebuilding"]:
            continue
        now = time.time()
        b = int((now - CLOSE_GRACE_SECS) // CANDLE_SECONDS)
        if rt["gap"] or (last_b is not None and b - last_b > 1):
            await notify(http, "WARNING: the scanner was paused for more than one candle (computer sleep or lost "
                               "connection). Reloading history from Cosmic. Setups that started during the pause "
                               "are NOT alerted.")
            pending.clear()
            await rebuild_all(http)
            last_b = int((time.time() - CLOSE_GRACE_SECS) // CANDLE_SECONDS)
            continue
        for x in list(states.values()):
            if advance(x, b):
                evaluate(x, now)
        if last_b is None:
            last_b = b
        elif b > last_b:
            write_coverage(last_b)
            last_b = b
        if pending:
            batch, pending[:] = list(pending), []
            t = asyncio.create_task(flush_alerts(http, batch))     # sending never blocks the candle loop
            bg_tasks.add(t)
            t.add_done_callback(bg_tasks.discard)


async def status_loop():
    warned = False
    while True:
        await asyncio.sleep(60)
        total = len(states)
        with_ticks = sum(1 for s in states.values() if s.ticks)
        ready = sum(1 for s in states.values() if len(s.candles) >= MIN_CANDLES)
        log.info("status: %d options | %d received ticks | %d warmed up (>=%d candles) | %d msgs/min | BTC %s",
                 total, with_ticks, ready, MIN_CANDLES, stats["msgs"], btc["price"])
        stats["msgs"] = 0
        if total and with_ticks == 0 and not warned and time.time() - stats["start"] > 90:
            warned = True
            log.error("NO TICKS received for any option symbol. The /feeds stream may not carry option "
                      "contracts (the docs only show perpetuals). Ask Cosmic support, or check symbol names.")


async def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    log.info("starting | base=%s | candle=%ss | Telegram=%s | charts=%s", BASE_URL, CANDLE_SECONDS,
             f"on ({len(TELEGRAM_CHATS)} recipient(s))" if TELEGRAM_TOKEN and TELEGRAM_CHATS else "off (console + csv only)",
             "on" if CHARTS and HAVE_MPL else ("off (matplotlib not installed)" if CHARTS else "off"))
    async with aiohttp.ClientSession() as http:
        if TELEGRAM_TOKEN and TELEGRAM_CHATS:     # proves Telegram works right away
            await notify(http, f"Cosmic scanner started ({CANDLE_SECONDS / 60:g}m candles). "
                               f"You will get a message here when a setup starts.")
        await asyncio.gather(contracts_loop(http), roll_loop(http), status_loop())


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass
