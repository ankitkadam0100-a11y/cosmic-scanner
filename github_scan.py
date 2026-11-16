#!/usr/bin/env python3
"""
github_scan.py - ONE-SHOT version of the scanner, made to run on GitHub Actions every 15 minutes.
Places no orders. Uses the same maths, setup rule and filters as cosmic_scanner.py (it imports it).

Each run:
  1. lists every active BTC option on Cosmic (all expiries),
  2. downloads Cosmic's official 15-minute mark-price history for each,
  3. finds every moment the setup STARTED (Supertrend(10,3) bearish AND EMA50 > EMA20, Heikin Ashi)
     in the last LOOKBACK_CANDLES closed candles (default 8 = 2 hours, so a late or skipped run
     does not lose a signal),
  4. skips signals it already sent (remembered in state/alerted.json),
  5. applies the filters (price, spread, time to expiry, late signal),
  6. sends one grouped Telegram message plus chart images,
  7. saves its memory back to the repository (state/ folder) - the workflow does the saving.

First run: it only remembers what already exists (no alert flood) and sends "scanner is live".
Secrets (set in GitHub, never in a file): TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID (comma-separated).
"""
import asyncio
import csv
import json
import logging
import os
import sys
import time
from datetime import datetime, timedelta, timezone

import aiohttp

import cosmic_scanner as cs

C = cs.CANDLE_SECONDS
IST = cs.IST
LOOKBACK = int(os.getenv("LOOKBACK_CANDLES", "8"))
STATE_DIR = os.getenv("STATE_DIR", "state")
STATE_FILE = os.path.join(STATE_DIR, "alerted.json")
LOG_FILE = os.path.join(STATE_DIR, "signals_log.csv")
DRY_RUN = os.getenv("DRY_RUN") == "1"          # testing only: console instead of Telegram
HEARTBEAT_HOUR_IST = 9                          # one "still running" message a day, after this hour
log = logging.getLogger("github_scan")


# ------------------------------------------------------------------ state
def load_state():
    try:
        with open(STATE_FILE) as f:
            return json.load(f)
    except Exception:
        return {"bootstrapped": False, "alerted": {}, "last_heartbeat": ""}


def save_state(state, now):
    state["alerted"] = {k: v for k, v in state["alerted"].items() if now - v < 3 * 86400}
    os.makedirs(STATE_DIR, exist_ok=True)
    with open(STATE_FILE, "w") as f:
        json.dump(state, f, indent=1, sort_keys=True)


def log_signal(row):
    os.makedirs(STATE_DIR, exist_ok=True)
    new = not os.path.exists(LOG_FILE)
    with open(LOG_FILE, "a", newline="") as f:
        w = csv.writer(f)
        if new:
            w.writerow(["checked_utc", "symbol", "signal_candle_ist", "mark", "spread_pct", "mins_to_expiry",
                        "alerted", "reason"])
        w.writerow(row)


# ------------------------------------------------------------------ data
async def get_json(http, url, sem=None, tries=3):
    for _ in range(tries):
        try:
            if sem:
                async with sem:
                    async with http.get(url, timeout=aiohttp.ClientTimeout(total=30)) as r:
                        if r.status == 429:
                            await asyncio.sleep(float(r.headers.get("Retry-After", "2")))
                            continue
                        return (await r.json()) if r.status == 200 else None
            else:
                async with http.get(url, timeout=aiohttp.ClientTimeout(total=30)) as r:
                    return (await r.json()) if r.status == 200 else None
        except Exception:
            await asyncio.sleep(1)
    return None


async def fetch_history(http, sem, sym, now):
    url = (f"{cs.BASE_URL}/api/v1/charts/{sym}/mark-klines?interval={max(1, C // 60)}"
           f"&from={now - 300 * C}&to={now + C}")
    bars = await get_json(http, url, sem)
    if not isinstance(bars, list):
        return None
    cur = now // C
    out = []
    for b in bars:
        try:
            if int(b["time"]) // C < cur:                       # closed candles only
                out.append((int(b["time"]) // C, float(b["open"]), float(b["high"]),
                            float(b["low"]), float(b["close"])))
        except Exception:
            continue
    return out


async def fetch_spread(http, sym):
    d = await get_json(http, f"{cs.BASE_URL}/api/v1/orderbook/{sym}?depth=1", tries=1)
    try:
        bid, ask = float(d["bids"][0]["price"]), float(d["asks"][0]["price"])
        if bid > 0 and ask > 0:
            return (ask - bid) / ((ask + bid) / 2) * 100
    except Exception:
        pass
    return None                                                  # unknown -> spread filter not applied


def find_starts(candles):
    """Every candle where the setup started (same rule as the live scanner)."""
    s = cs.compute_series(candles)
    out, prev = [], None
    for i in range(len(candles)):
        if s["dir"][i] is None or s["ema_slow"][i] is None or i + 1 < cs.MIN_CANDLES:
            prev = None
            continue
        r = {k: s[k][i] for k in ("ha_open", "ha_high", "ha_low", "ha_close", "st", "dir", "ema_fast", "ema_slow")}
        bear = cs.is_bearish(r)
        if bear and prev is False:
            out.append({"i": i, "bucket": candles[i][0], "r": r})
        prev = bear
    return out


# ------------------------------------------------------------------ telegram
async def send_text(http, text):
    """True if at least one recipient got it."""
    print(text, flush=True)
    if DRY_RUN:
        return True
    if not (cs.TELEGRAM_TOKEN and cs.TELEGRAM_CHATS):
        log.error("Telegram is not configured (secrets TELEGRAM_BOT_TOKEN / TELEGRAM_CHAT_ID missing)")
        return False
    ok = False
    for chat in cs.TELEGRAM_CHATS:
        try:
            async with http.post(f"https://api.telegram.org/bot{cs.TELEGRAM_TOKEN}/sendMessage",
                                 json={"chat_id": chat, "text": text[:4000]},
                                 timeout=aiohttp.ClientTimeout(total=20)) as resp:
                if resp.status == 200:
                    ok = True
                else:
                    log.warning("Telegram error for chat %s: %s %s", chat, resp.status, (await resp.text())[:150])
        except Exception as e:
            log.warning("Telegram send failed for chat %s: %r", chat, e)
    return ok


# ------------------------------------------------------------------ main
async def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    now = int(time.time())
    cur = now // C
    state = load_state()
    first_run = not state.get("bootstrapped")
    now_ist = datetime.fromtimestamp(now, IST)
    failed = False

    async with aiohttp.ClientSession() as http:
        opts = await cs.fetch_contracts(http)                    # {symbol: (kind, strike, expiry)}
        if not opts:
            log.error("no BTC options returned by Cosmic")
            sys.exit(1)
        sem = asyncio.Semaphore(6)
        syms = list(opts)
        res = await asyncio.gather(*(fetch_history(http, sem, s, now) for s in syms))
        hist = {s: h for s, h in zip(syms, res) if h}
        log.info("options listed: %d | history loaded: %d", len(opts), len(hist))
        if len(hist) < 0.5 * len(opts):
            log.error("history failed for more than half of the options (Cosmic blocked this server, or is down?)")
            sys.exit(1)
        btc = await fetch_history(http, sem, "BTCUSDT", now)
        cs.btc["price"] = btc[-1][4] if btc else None

        new = []
        for sym, h in hist.items():
            if len(h) < cs.MIN_CANDLES:
                continue
            kind, strike, exp = opts[sym]
            for st in find_starts(h):
                if not (cur - LOOKBACK <= st["bucket"] <= cur - 1):
                    continue
                key = f"{sym}|{st['bucket']}"
                if key in state["alerted"]:
                    continue
                new.append((sym, kind, strike, exp, h, st, key))
        log.info("new setup starts in the last %d candles: %d", LOOKBACK, len(new))

        if first_run:                                            # remember, do not alert
            for *_, key in new:
                state["alerted"][key] = now
            state["bootstrapped"] = True
            state["last_heartbeat"] = now_ist.strftime("%Y-%m-%d")
            ok = await send_text(http, f"GitHub scanner is live. Watching {len(hist)} BTC options "
                                       f"({CANDLES_TXT()} candles, Supertrend({cs.ST_PERIOD},{cs.ST_MULT:g}) "
                                       f"bearish + EMA50>EMA20). You will get a message here when a setup starts. "
                                       f"({len(new)} setups already running were ignored.)")
            save_state(state, now)
            sys.exit(0 if ok else 1)

        # apply filters
        alerts, skipped = [], []
        for sym, kind, strike, exp, h, st, key in new:
            i, r = st["i"], st["r"]
            mark = h[-1][4]
            mins_left = (exp - now) / 60
            reason = cs.filter_reason(mark, None, mins_left, r)
            spread = None
            if reason == "":
                spread = await fetch_spread(http, sym)
                reason = cs.filter_reason(mark, spread, mins_left, r)
            ct = datetime.fromtimestamp((st["bucket"] + 1) * C, IST).strftime("%d %b %H:%M")
            sig = {"sym": cs.Sym(sym, "CALL" if kind == "CALL" else "PUT", strike, exp), "mark": mark,
                   "spread": spread, "mins_left": mins_left, "r": r, "candle": ct, "candles": h[:i + 1]}
            log_signal([datetime.fromtimestamp(now, timezone.utc).strftime("%Y-%m-%d %H:%M:%S"), sym, ct,
                        round(mark, 2), None if spread is None else round(spread, 2), round(mins_left),
                        reason == "", reason])
            (alerts if reason == "" else skipped).append((sig, key))
        for sig, key in skipped:
            state["alerted"][key] = now                          # filtered: never retried

        if alerts:
            alerts.sort(key=lambda a: (a[0]["sym"].expiry, a[0]["sym"].kind, a[0]["sym"].strike))
            lines = [f"[{a[0]['candle'][-5:]}] " + cs.fmt_line(a[0]) for a in alerts[:cs.MAX_ALERT_LINES]]
            if len(alerts) > cs.MAX_ALERT_LINES:
                lines.append(f"... +{len(alerts) - cs.MAX_ALERT_LINES} more (see state/signals_log.csv)")
            head = (f"NEW SETUP: Supertrend({cs.ST_PERIOD},{cs.ST_MULT:g}) bearish + EMA50>EMA20 | "
                    f"{C / 60:g}m Heikin Ashi | {len(alerts)} option(s) | [time] = signal candle closed (IST)")
            ok = await send_text(http, head + "\n" + "\n".join(lines))
            if ok:
                for sig, key in alerts:
                    state["alerted"][key] = now
                if cs.CHARTS and cs.HAVE_MPL and not DRY_RUN:
                    for sig, key in alerts[:cs.MAX_CHARTS_PER_BATCH]:
                        try:
                            png = await asyncio.to_thread(cs.render_chart, sig)
                            await cs.send_photo(http, png, cs.fmt_line(sig))
                        except Exception as e:
                            log.warning("chart failed for %s: %r", sig["sym"].name, e)
            else:
                failed = True                                    # not saved -> retried next run

        today = now_ist.strftime("%Y-%m-%d")
        if now_ist.hour >= HEARTBEAT_HOUR_IST and state.get("last_heartbeat") != today:
            if await send_text(http, f"Daily check: scanner is running. {len(hist)} BTC options checked at "
                                     f"{now_ist:%H:%M} IST."):
                state["last_heartbeat"] = today
        save_state(state, now)
    sys.exit(1 if failed else 0)


def CANDLES_TXT():
    return f"{C // 60}m"


if __name__ == "__main__":
    asyncio.run(main())
