import flet as ft
import yfinance as yf
import threading
import time
import math
import random
import csv
import json
import urllib.parse
import urllib.request
import os
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta

# ============================================================
# NIFTY PRO QUANT TERMINAL v18.5
# v18.4 CARRIED FORWARD AS-IS (all fixes + features unchanged):
#   - Engine 4 zone bug fix, chat race-condition fix, trade lock,
#     ledger crash-proofing, error logging, manual analysis panel,
#     auto-scan interval selector, market-hours indicator,
#     data-staleness timestamp, backtest color-code, capital guard
#
# NEW IN v18.5 (Manual Analysis upgrades only -- nothing else touched):
#   A) Date+Time tagged predictions, saved to a journal, later
#      verified against actual market data (manual button + auto
#      background check), with a rule-based diagnosis on misses.
#   B) Calculation improvements: confidence-weighted verdict,
#      multi-timeframe confirmation, risk:reward check,
#      volume-confirmed breakout check, rolling accuracy tracker
#      that flags the Manual Engine's own reliability over time.
# ============================================================

APP_VERSION = "18.8"
# v18.8 changes (v18.7 otherwise carried forward):
#   1. Verdict box now shows a proper trade plan: Entry, Target 1/2, Stoploss,
#      R:R, nearby Support/Resistance -- and for NO-TRADE it shows the CALL/PUT
#      trigger levels to wait for (instead of Entry=Target=SL=price).
#   2. ATR is now measured on 15-minute candles (built from the 1-min data
#      already fetched). The old 1-minute ATR (~1-2 pts) made targets/SL
#      meaningless. Risk Manager uses the same ATR, so both stay consistent.
#   3. Engine-4 anchor (previous close) fixed for pre-market/weekend: it used
#      the close from 2 sessions ago whenever today's candle did not exist yet.
#   4. Chart tooltip shows date+time along with the price (2 decimals).
#   5. Notepad moved into a pop-up (small button); its space now hosts
#      Price Alerts (saved to file, checked on every scan + a light poller).
#   6. Manual Analysis: accuracy-based auto-tuning of the minimum confidence,
#      and its Entry/Target/SL now use the same trade-plan logic.
# v18.7 changes (v18.6 fully carried forward otherwise):
#   1. Engine boxes (1-4) now stretch to equal height -- fixes Engine 2
#      looking squished next to the taller Engine 1 (news) box.
#   2. Manual Analysis verification now tries a same-day INTRADAY check
#      first (~30 min after your entry, using 1-min data) instead of
#      always waiting for the next trading day's close. Falls back to
#      the next-day-close method for older/out-of-range predictions.
#   3. Paper trading now blocks NEW entries when the market is closed
#      (existing positions can still be exited any time).
#   4. Trader's Notepad: notes are now click-to-expand/collapse.
#   5. Paper Trading rebuilt: Option Chain (ATM +/-3 strikes, CE & PE,
#      Buy buttons) + up to 3 simultaneous open positions with individual
#      Exit buttons, Exit All, and margin tracked across all open trades.

class AdaptiveQuantConfig:
    def __init__(self):
        self.atr_multiplier = 1.0
        self.optimization_score = 0.0

    def auto_tune(self, wins, losses, total):
        if total <= 0: return "No data to optimize."
        win_rate = (wins / total) * 100
        self.optimization_score = win_rate
        if win_rate < 70:
            self.atr_multiplier = 1.3
            return f"Accuracy low ({win_rate:.1f}%). ATR buffered to 1.3x."
        self.atr_multiplier = 1.0
        return f"Accuracy solid ({win_rate:.1f}%). Strategy stable."

quant_config = AdaptiveQuantConfig()

def safe_float(value, default=0.0):
    try: return float(value) if math.isfinite(float(value)) else default
    except: return default

def pct_change(current, previous):
    return ((current - previous) / previous) * 100.0 if previous else 0.0

def calculate_atr(df, period=14):
    if df is None or df.empty or len(df) < 2: return 0.0
    high, low, close = df["High"].astype(float), df["Low"].astype(float), df["Close"].astype(float)
    prev_close = close.shift(1)
    tr = (high - low).abs().combine((high - prev_close).abs(), max).combine((low - prev_close).abs(), max)
    return safe_float(tr.rolling(period, min_periods=1).mean().iloc[-1])

def calculate_vwap(df):
    if df is None or df.empty: return 0.0
    typical = (df["High"].astype(float) + df["Low"].astype(float) + df["Close"].astype(float)) / 3.0
    if "Volume" in df.columns:
        volume = df["Volume"].fillna(0).astype(float)
        if volume.sum() > 0: return safe_float((typical * volume).sum() / volume.sum())
    return safe_float(typical.mean())

def calculate_volume_signal(df):
    if df is None or df.empty or "Volume" not in df.columns: return "Volume unavailable", 0.0
    volume = df["Volume"].fillna(0).astype(float)
    if len(volume) < 6 or volume.sum() == 0: return "Volume unavailable", 0.0
    current = safe_float(volume.iloc[-1])
    baseline = safe_float(volume.iloc[-6:-1].mean())
    if baseline <= 0: return "Volume unavailable", 0.0
    change = ((current - baseline) / baseline) * 100.0
    if change >= 25: return f"Volume surge (+{change:.0f}%)", change
    if change <= -25: return f"Volume contraction ({change:.0f}%)", change
    return f"Volume normal ({change:+.0f}%)", change

def calculate_pivots(day_high, day_low, prev_close):
    pivot = (day_high + day_low + prev_close) / 3.0
    return pivot, (2 * pivot) - day_high, (2 * pivot) - day_low

def fetch_history(symbol, period="5d", interval="1m"):
    return yf.Ticker(symbol).history(period=period, interval=interval, auto_adjust=False, prepost=False, timeout=7)

def get_simulated_option_ltp(spot, strike, opt_type, vix):
    vix = safe_float(vix, 14.0)
    distance = abs(spot - strike)
    intrinsic = max(0, spot - strike) if opt_type == "CE" else max(0, strike - spot)
    extrinsic = (max(vix, 12.0) / 15.0) * 80.0 * math.exp(-distance / 80.0)
    return round(intrinsic + extrinsic, 2)

# ------------------------------------------------------------
# v18.8 TRADE-PLAN HELPERS (pure functions, no UI)
# ------------------------------------------------------------
def resolve_prev_session(daily_df, fallback_price, today=None):
    """Return (prev_close, prev_high, prev_low) of the reference session.
    If the latest daily candle is today's, the reference is the one before it.
    If today has no candle yet (pre-market / weekend / holiday), the latest
    candle IS the last completed session, so it is the reference."""
    try:
        if daily_df is None or daily_df.empty:
            return fallback_price, fallback_price, fallback_price
        d = daily_df.dropna(subset=["High", "Low", "Close"])
        if d.empty:
            return fallback_price, fallback_price, fallback_price
        today = today or datetime.now().date()
        if d.index[-1].date() >= today and len(d) >= 2:
            row = d.iloc[-2]
        else:
            row = d.iloc[-1]
        return (safe_float(row["Close"], fallback_price),
                safe_float(row["High"], fallback_price),
                safe_float(row["Low"], fallback_price))
    except Exception:
        return fallback_price, fallback_price, fallback_price

def estimate_atr_15m(df, period=14):
    """ATR on 15-minute candles built from 1-minute data (no extra network call)."""
    try:
        ohlc = df[["Open", "High", "Low", "Close"]].astype(float)
        df15 = ohlc.resample("15min").agg({"Open": "first", "High": "max", "Low": "min", "Close": "last"}).dropna()
        if len(df15) >= 3:
            v = calculate_atr(df15, period)
            if v > 0:
                return v
    except Exception:
        pass
    return calculate_atr(df, period) * math.sqrt(15)  # random-walk scaling fallback

def collect_levels(prev_high, prev_low, prev_close, session_high, session_low):
    """Nearby reference levels: previous-session H/L/C, classic pivot, R1/R2/S1/S2,
    plus the latest session's high/low."""
    levels = []
    if prev_high > 0 and prev_low > 0 and prev_close > 0:
        p = (prev_high + prev_low + prev_close) / 3.0
        rng = prev_high - prev_low
        levels += [prev_high, prev_low, prev_close, p, 2 * p - prev_low, 2 * p - prev_high, p + rng, p - rng]
    levels += [session_high, session_low]
    return sorted({round(l, 1) for l in levels if l and l > 0})

def nearby_levels(price, levels, count=2):
    """Nearest `count` levels on each side of price. When price is beyond every known level
    (e.g. sitting at the session high/low) the gap is filled with round 50-point numbers,
    which traders watch anyway -- so Support/Resistance is never left blank."""
    below = sorted([l for l in levels if l < price - 0.5], reverse=True)[:count]
    above = sorted([l for l in levels if l > price + 0.5])[:count]
    step = 50.0
    c = math.floor((price - 0.5) / step) * step
    while len(below) < count and c > 0:
        if all(abs(c - b) > 5 for b in below): below.append(c)
        c -= step
    c = math.ceil((price + 0.5) / step) * step
    while len(above) < count:
        if all(abs(c - a) > 5 for a in above): above.append(c)
        c += step
    return sorted(below, reverse=True), sorted(above)

def fmt_levels(vals, levels):
    """'23018 / 23004'; a trailing * marks a round-number fallback level."""
    real = {round(l, 1) for l in levels}
    return " / ".join(f"{x:.0f}" + ("" if round(x, 1) in real else "*") for x in vals) if vals else "--"

def build_trade_plan(direction, entry, atr, levels):
    """Volatility-based plan. SL = 1.5 x ATR(15m) (same multiple the app already used),
    Target 1 = 1.5R, Target 2 = 2.5R. Target 1 is pulled back below the first
    resistance (long) / above the first support (short) if that comes earlier."""
    sl_dist = max(atr * 1.5, 1.0)
    capped_by = None
    if direction == "LONG":
        sl = entry - sl_dist
        t1, t2 = entry + sl_dist * 1.5, entry + sl_dist * 2.5
        blockers = sorted(l for l in levels if l > entry + 0.3 * sl_dist)
        if blockers and blockers[0] < t1:
            capped_by = blockers[0]
            t1 = max(blockers[0] - 0.1 * sl_dist, entry + 0.2 * sl_dist)
    else:
        sl = entry + sl_dist
        t1, t2 = entry - sl_dist * 1.5, entry - sl_dist * 2.5
        blockers = sorted((l for l in levels if l < entry - 0.3 * sl_dist), reverse=True)
        if blockers and blockers[0] > t1:
            capped_by = blockers[0]
            t1 = min(blockers[0] + 0.1 * sl_dist, entry - 0.2 * sl_dist)
    rr = abs(t1 - entry) / sl_dist
    quality = "Good" if rr >= 1.3 else "OK" if rr >= 0.9 else "Poor"
    return {"direction": direction, "entry": entry, "sl": sl, "t1": t1, "t2": t2,
            "rr": rr, "quality": quality, "capped_by": capped_by}

# ------------------------------------------------------------
# Engine 4 zone bug fix (from v18.4, unchanged): the original
# "e3 <= ltp <= e8" condition could never be True. e9 (the
# already-defined-but-unused lower mirror of e3) is used here.
# ------------------------------------------------------------
def calculate_engine_4(ltp, anchor):
    e3, e4, e5, e6 = anchor + 150, anchor + 100, anchor + 50, anchor + 20
    e7, e8, e9 = anchor - 20, anchor - 50, anchor - 100
    if e7 <= ltp <= e6: state, bias = "NO TRADE (Inside NTZ)", "NEUTRAL"
    elif ltp > e6: state, bias = "CE ENTRY ON BREAKOUT", "BULLISH"
    elif ltp < e7: state, bias = "PE ENTRY ON BREAKDOWN", "BEARISH"
    else: state, bias = "WAIT FOR SIGNAL", "NEUTRAL"
    strike = round(ltp / 50) * 50
    opt_type = "CE" if bias == "BULLISH" else "PE" if bias == "BEARISH" else "WAIT"
    if ltp >= e3 or ltp <= e9: zone = "EXTREME: Avoid Fresh"
    elif (e4 <= ltp < e3) or (e7 >= ltp > e8): zone = "HIGH RISK: Retest"
    elif (e5 <= ltp < e4) or (e6 >= ltp > e7): zone = "MODERATE: Confirm"
    else: zone = "SAFE: Near Anchor"
    return bias, state, strike, opt_type, zone

def classify_news(text):
    t = str(text).lower()
    bull = sum(1 for w in ["rate cut", "cuts rates", "easing", "stimulus", "growth", "rally", "bullish", "strong demand", "lower inflation", "liquidity", "support", "recovery", "dovish"] if w in t)
    bear = sum(1 for w in ["rate hike", "hikes rates", "tariff", "sanction", "war", "crash", "bearish", "recession", "higher inflation", "hawkish", "selloff", "selling", "weak demand"] if w in t)
    if bull > bear: return "BULLISH"
    if bear > bull: return "BEARISH"
    return "NEUTRAL"

# ============================================================
# GOOGLE NEWS RSS INTEGRATION
# ============================================================
def fetch_live_news():
    try:
        url = "https://news.google.com/rss/search?q=Nifty+50+OR+Indian+Stock+Market+OR+Sensex&hl=en-IN&gl=IN&ceid=IN:en"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"})
        with urllib.request.urlopen(req, timeout=10) as r:
            xml_data = r.read()

        root = ET.fromstring(xml_data)
        cleaned, total_bull, total_bear = [], 0, 0

        for item in root.findall(".//item")[:5]:
            title = str(item.find("title").text).strip()
            if not title: continue

            if " - " in title: title = title.rsplit(" - ", 1)[0]

            sent = classify_news(title)
            if sent == "BULLISH": total_bull += 1
            elif sent == "BEARISH": total_bear += 1
            cleaned.append({"title": title, "sentiment": sent})

        if not cleaned: return "NEUTRAL", [{"title": "Market steady, tracking global cues.", "sentiment": "NEUTRAL"}]
        overall = "BULLISH" if total_bull > total_bear else "BEARISH" if total_bear > total_bull else "NEUTRAL"
        return overall, cleaned
    except Exception:
        return "NEUTRAL", [{"title": "Live macro feed connecting... monitoring price action.", "sentiment": "NEUTRAL"}]

# ============================================================
# MARKET HOURS HELPER
# ============================================================
def is_market_open(now=None):
    now = now or datetime.now()
    if now.weekday() >= 5:
        return False
    market_open = now.replace(hour=9, minute=15, second=0, microsecond=0)
    market_close = now.replace(hour=15, minute=30, second=0, microsecond=0)
    return market_open <= now <= market_close

# ============================================================
# SMART DESI AI MENTOR (WITH EXACT MATH PROCESS)
# ============================================================
def generate_smart_reply(q, state):
    q = q.lower()
    p, v, m, reason, vdt = state["price"], state["vwap"], state["macro"], state["latest_reason"], state["verdict"]
    anchor = state.get("anchor", 0.0)

    if any(w in q for w in ["hello", "hi", "kaise ho", "kya haal"]):
        return "Arre bhai! Main ekdum badiya. Tu bata, aaj market mein aag lagani hai ya aaram karna hai? 'Math' likh kar logic samajh!"
    if any(w in q for w in ["joke", "hasao", "laugh"]):
        return "Ek trader mandir gaya aur bola: 'Bhagwan, bas ek bull run de do, top pe exit karunga!' Bhagwan bole: 'Pichle 3 baar se yahi bol raha hai, chup chap SL laga!'"

    if any(w in q for w in ["samjha", "explain", "detail", "kyu", "why", "setup", "math", "calc", "process"]):
        trend_dir = "BULLISH 📈" if p >= v else "BEARISH 📉"
        diff_vwap = p - v
        e6, e7 = anchor + 20, anchor - 20
        diff_anchor = p - anchor
        e4_bias = "BULLISH Breakout" if p > e6 else "BEARISH Breakdown" if p < e7 else "NEUTRAL (Inside NTZ)"

        math_response = (
            f"🧮 [MATH & LOGIC PROCESS EXECUTED]\n\n"
            f"1️⃣ VWAP ENGINE (Trend Calculation):\n"
            f"➜ Formula: Current Price - VWAP\n"
            f"➜ Math: ₹{p:.1f} - ₹{v:.1f} = {diff_vwap:+.1f} points\n"
            f"➜ Result: Trend is {trend_dir}.\n\n"
            f"2️⃣ ENGINE 4 (Anchor Breakdown/Breakout):\n"
            f"➜ Formula: Anchor (Prev Close ₹{anchor:.1f}) ± 20 pts\n"
            f"➜ No-Trade-Zone (NTZ) Limits: ₹{e7:.1f} to ₹{e6:.1f}\n"
            f"➜ Current Status: Price vs Anchor = {diff_anchor:+.1f} pts\n"
            f"➜ Result: Setup is {e4_bias}.\n\n"
            f"3️⃣ FINAL VERDICT GENERATION:\n"
            f"➜ If Trend AND Engine 4 match, trade is generated.\n"
            f"➜ Current Output = {vdt}."
        )
        return math_response

    if any(w in q for w in ["news", "macro", "duniya"]):
        return f"Aaj global aur local news ka sentiment '{m}' hai. Live ticker par nazar rakh. News trend ke against heavy lot size mat uthana."

    return f"Main data ke hisaab se track kar raha hu: Verdict '{vdt}' hai. Exact calculation dekhni hai toh 'math' ya 'kyun' type kar!"

# ============================================================
# MAIN APPLICATION
# ============================================================
def main(page: ft.Page):
    page.title = f"NIFTY PRO QUANT MOBILE v{APP_VERSION}"
    page.theme_mode = ft.ThemeMode.DARK
    page.bgcolor = "#020409"
    page.padding = 10
    try: page.window.maximized = True
    except: pass

    state = {
        "scanning": False, "scan_lock": threading.Lock(), "trade_lock": threading.Lock(),
        "pred_lock": threading.Lock(), "running": True,
        "price": 0.0, "vwap": 0.0, "anchor": 0.0, "macro": "NEUTRAL", "verdict": "WAIT", "vix": 14.0,
        "atr": 0.0, "volume_change_pct": 0.0,
        "latest_reason": "Run live scan to generate analysis.",
        "capital": 100000.0, "peak_capital": 100000.0, "max_drawdown_pct": 0.0,
        "wins": 0, "losses": 0, "trade_count": 0, "current_streak": 0, "glitch_logs": [],
        "positions": [], "order_lots": 1, "atm_strike": 0, "chain": {},
        "levels": [], "alerts": [], "alert_lock": threading.Lock(), "last_scan_ts": 0.0,
        "news_items": [], "notes": [], "predictions": []
    }

    def log_glitch(module, issue):
        ts = datetime.now().strftime("%H:%M:%S")
        state["glitch_logs"].append(f"[{ts}] {module}: {issue}")
        if len(state["glitch_logs"]) > 50: state["glitch_logs"].pop(0)

    # ================= LEFT PANEL (RISK, MENTOR & REAL NOTEPAD) =================
    big_money_status = ft.Text("Scanning flow...", size=11, color=ft.colors.YELLOW_300, weight=ft.FontWeight.BOLD)
    volume_spike_status = ft.Text("Analyzing volume...", size=11, color=ft.colors.CYAN_300, weight=ft.FontWeight.BOLD)
    oi_change_status = ft.Text("Live stream ready", size=11, color=ft.colors.PURPLE_300, weight=ft.FontWeight.BOLD)

    risk_per_trade_txt = ft.Text("₹0 (2%)", size=12, color=ft.colors.RED_300, weight=ft.FontWeight.BOLD)
    sl_points_txt = ft.Text("0 pts", size=12, color=ft.colors.YELLOW_300, weight=ft.FontWeight.BOLD)
    safe_lots_txt = ft.Text("0 Lots", size=12, color=ft.colors.GREEN_300, weight=ft.FontWeight.BOLD)

    chat_list = ft.ListView(expand=True, spacing=4, auto_scroll=True)
    chat_list.controls.append(ft.Text("🤖 Mentor: Bhai bata, aaj kya trade karna hai? Setup ki exact 'math' pucho toh logic dikha dunga.", size=10, color=ft.colors.CYAN_200))

    def send_ai_message(e):
        q = user_input.value.strip()
        if not q: return
        chat_list.controls.append(ft.Text(f"👤 Tu: {q}", size=10, color=ft.colors.WHITE))
        user_input.value = ""
        chat_list.controls.append(ft.Text("🤖 Mentor: Calculating logic...", size=10, color=ft.colors.CYAN_300))
        placeholder_index = len(chat_list.controls) - 1
        chat_list.update()

        def worker():
            ans = generate_smart_reply(q, state)
            time.sleep(0.5)
            try:
                chat_list.controls[placeholder_index] = ft.Text(f"🤖 Mentor:\n{ans}", size=10, color=ft.colors.CYAN_200)
                chat_list.update()
            except Exception as ex:
                log_glitch("Chat Mentor", str(ex))

        threading.Thread(target=worker, daemon=True).start()

    user_input = ft.TextField(hint_text="Ask bhai... (try 'math' or 'why')", expand=True, bgcolor="#020409", border_color=ft.colors.WHITE24, text_size=11, height=35, content_padding=8, on_submit=send_ai_message)

    # --- ADVANCED NOTEPAD SYSTEM ---
    def load_notes():
        if os.path.exists("nifty_notes.json"):
            try:
                with open("nifty_notes.json", "r", encoding="utf-8") as f: return json.load(f)
            except Exception as ex:
                log_glitch("Notes Load", str(ex))
                return []
        return []

    def save_notes():
        try:
            with open("nifty_notes.json", "w", encoding="utf-8") as f: json.dump(state["notes"], f)
        except Exception as ex:
            log_glitch("Notes Save", str(ex))

    # --- PREDICTION JOURNAL (NEW in v18.5) ---
    def load_predictions():
        if os.path.exists("nifty_manual_predictions.json"):
            try:
                with open("nifty_manual_predictions.json", "r", encoding="utf-8") as f: return json.load(f)
            except Exception as ex:
                log_glitch("Predictions Load", str(ex))
                return []
        return []

    def save_predictions():
        try:
            with open("nifty_manual_predictions.json", "w", encoding="utf-8") as f: json.dump(state["predictions"], f)
        except Exception as ex:
            log_glitch("Predictions Save", str(ex))

    state["notes"] = load_notes()
    state["predictions"] = load_predictions()
    notes_list = ft.ListView(expand=True, spacing=4, auto_scroll=True)
    notes_expanded = set()  # runtime-only (not persisted): which note indices are currently expanded

    def toggle_note(idx):
        if idx in notes_expanded: notes_expanded.discard(idx)
        else: notes_expanded.add(idx)
        render_notes()

    def render_notes():
        notes_list.controls.clear()
        if not state["notes"]: notes_list.controls.append(ft.Text("No notes added yet.", size=9, color=ft.colors.WHITE54))
        for i, note in enumerate(state["notes"]):
            def make_delete(index): return lambda e: delete_note(index)
            def make_toggle(index): return lambda e: toggle_note(index)
            is_open = i in notes_expanded
            full_text = note["text"]
            preview = full_text if is_open else (full_text[:40] + ("..." if len(full_text) > 40 else ""))
            note_ui = ft.Container(
                bgcolor="#070C1E", padding=6, border_radius=6, border=ft.border.all(1, ft.colors.WHITE10),
                on_click=make_toggle(i),
                content=ft.Row([
                    ft.Column([
                        ft.Row([
                            ft.Text(note["time"], size=8, color=ft.colors.YELLOW_400, weight=ft.FontWeight.BOLD),
                            ft.Icon(ft.icons.EXPAND_LESS if is_open else ft.icons.EXPAND_MORE, size=12, color=ft.colors.WHITE38)
                        ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
                        ft.Text(preview, size=10, color=ft.colors.WHITE)
                    ], expand=True, spacing=2),
                    ft.IconButton(ft.icons.DELETE, icon_color=ft.colors.RED_400, icon_size=14, on_click=make_delete(i))
                ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN, vertical_alignment=ft.CrossAxisAlignment.START)
            )
            notes_list.controls.append(note_ui)
        try: notes_list.update()
        except: pass

    def delete_note(idx):
        if 0 <= idx < len(state["notes"]):
            state["notes"].pop(idx)
            save_notes()
            render_notes()

    def add_new_note(e):
        val = notepad_input.value.strip()
        if val:
            ts = datetime.now().strftime("%d %b %Y, %I:%M %p")
            state["notes"].append({"time": ts, "text": val})
            save_notes()
            notepad_input.value = ""
            notepad_input.update()
            render_notes()

    notepad_input = ft.TextField(hint_text="Type data & press Add ➜", expand=True, text_size=10, height=35, content_padding=8, bgcolor="#020409", border_color=ft.colors.WHITE24, on_submit=add_new_note)

    # ---------- v18.8: Notepad now opens as a pop-up from a small button ----------
    def open_notepad(e):
        render_notes()
        notepad_dialog.open = True
        page.update()

    def close_notepad(e=None):
        notepad_dialog.open = False
        page.update()

    notepad_dialog = ft.AlertDialog(
        title=ft.Text("📝 TRADER'S NOTEPAD", color=ft.colors.YELLOW_400, weight=ft.FontWeight.BOLD),
        content=ft.Container(width=320, height=380, content=ft.Column([
            ft.Container(content=notes_list, expand=True, bgcolor="#020409", padding=4, border_radius=6),
            ft.Row([notepad_input, ft.ElevatedButton("Add", bgcolor=ft.colors.YELLOW_800, color="white", height=35, on_click=add_new_note)], spacing=4)
        ], spacing=6)),
        actions=[ft.ElevatedButton("Close", on_click=close_notepad)]
    )
    page.overlay.append(notepad_dialog)

    # ---------- v18.8: PRICE ALERTS (saved to nifty_alerts.json) ----------
    def load_alerts():
        if os.path.exists("nifty_alerts.json"):
            try:
                with open("nifty_alerts.json", "r", encoding="utf-8") as f: return json.load(f)
            except Exception as ex:
                log_glitch("Alerts Load", str(ex))
                return []
        return []

    def save_alerts():
        try:
            with open("nifty_alerts.json", "w", encoding="utf-8") as f: json.dump(state["alerts"], f)
        except Exception as ex:
            log_glitch("Alerts Save", str(ex))

    state["alerts"] = load_alerts()
    alerts_list = ft.ListView(expand=True, spacing=4, auto_scroll=False)
    alert_msg_txt = ft.Text("", size=9, color=ft.colors.WHITE54)
    alert_price_input = ft.TextField(hint_text="Price", width=88, height=35, text_size=10, content_padding=6, bgcolor="#020409", border_color=ft.colors.WHITE24, keyboard_type=ft.KeyboardType.NUMBER)
    alert_label_input = ft.TextField(hint_text="Label (optional)", expand=True, height=35, text_size=10, content_padding=6, bgcolor="#020409", border_color=ft.colors.WHITE24)
    alert_cond_dd = ft.Dropdown(width=104, height=35, text_size=10, content_padding=5, value="ABOVE", options=[ft.dropdown.Option("ABOVE", "Above ▲"), ft.dropdown.Option("BELOW", "Below ▼")])

    alert_banner_text = ft.Text("", size=12, weight=ft.FontWeight.BOLD, color=ft.colors.YELLOW_400, expand=True)
    def dismiss_alert_banner(e=None):
        alert_banner.visible = False
        try: alert_banner.update()
        except Exception: pass
    alert_banner = ft.Container(
        visible=False, bgcolor="#3A2A00", padding=8, border_radius=8, border=ft.border.all(1, ft.colors.YELLOW_400), on_click=dismiss_alert_banner,
        content=ft.Row([alert_banner_text, ft.Text("(click to dismiss)", size=9, color=ft.colors.WHITE54)], alignment=ft.MainAxisAlignment.SPACE_BETWEEN)
    )

    def set_alert_msg(text, color):
        alert_msg_txt.value, alert_msg_txt.color = text, color
        try: alert_msg_txt.update()
        except Exception: pass

    def make_alert_delete(aid):
        def _delete(e):
            with state["alert_lock"]:
                state["alerts"] = [a for a in state["alerts"] if a["id"] != aid]
                save_alerts()
            render_alerts()
        return _delete

    def render_alerts():
        try:
            alerts_list.controls.clear()
            with state["alert_lock"]:
                items = list(state["alerts"])
            active = [a for a in items if not a.get("triggered")]
            done = [a for a in items if a.get("triggered")][::-1]
            if not items:
                alerts_list.controls.append(ft.Text("No alerts yet. Add a price level above.", size=9, color=ft.colors.WHITE54))
            for a in active + done:
                arrow = "▲ Above" if a["cond"] == "ABOVE" else "▼ Below"
                label = f" - {a['label']}" if a.get("label") else ""
                if a.get("triggered"):
                    txt = f"✅ {arrow} {a['price']:,.1f}{label}\n    hit @ {a['triggered_price']:,.1f}  ({a['triggered_at']})"
                    color = ft.colors.GREEN_400
                else:
                    txt = f"🔔 {arrow} {a['price']:,.1f}{label}"
                    color = ft.colors.YELLOW_400
                alerts_list.controls.append(ft.Container(
                    bgcolor="#070C1E", padding=6, border_radius=6, border=ft.border.all(1, ft.colors.WHITE10),
                    content=ft.Row([
                        ft.Text(txt, size=10, color=color, expand=True),
                        ft.IconButton(ft.icons.DELETE, icon_color=ft.colors.RED_400, icon_size=14, on_click=make_alert_delete(a["id"]))
                    ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN)
                ))
            try: alerts_list.update()
            except Exception: pass
        except Exception as ex:
            log_glitch("Alerts UI", str(ex))

    def add_alert(e):
        target = safe_float((alert_price_input.value or "").strip().replace(",", ""), -1.0)
        if target <= 0:
            set_alert_msg("⚠️ Enter a valid price.", ft.colors.RED_300)
            return
        cond = alert_cond_dd.value or "ABOVE"
        cur = state["price"]
        if cur > 0 and ((cond == "ABOVE" and cur >= target) or (cond == "BELOW" and cur <= target)):
            set_alert_msg(f"⚠️ Price is already {'above' if cond == 'ABOVE' else 'below'} {target:,.1f} (now {cur:,.1f}) - it would fire instantly.", ft.colors.RED_300)
            return
        with state["alert_lock"]:
            state["alerts"].append({
                "id": datetime.now().strftime("%H%M%S%f") + f"_{random.randint(100, 999)}",
                "price": target, "cond": cond, "label": (alert_label_input.value or "").strip(),
                "created": datetime.now().strftime("%d %b %H:%M"),
                "triggered": False, "triggered_at": None, "triggered_price": None
            })
            save_alerts()
        alert_price_input.value = ""; alert_label_input.value = ""
        try: alert_price_input.update(); alert_label_input.update()
        except Exception: pass
        set_alert_msg(f"✅ Alert set: {'Above' if cond == 'ABOVE' else 'Below'} {target:,.1f}" + ("" if cur > 0 else "  (run LIVE SCAN once so it can be validated)"), ft.colors.GREEN_400)
        render_alerts()

    def use_live_price(e):
        if state["price"] > 0:
            alert_price_input.value = f"{state['price']:.1f}"
            try: alert_price_input.update()
            except Exception: pass
        else:
            set_alert_msg("⚠️ Run LIVE SCAN first to get the live price.", ft.colors.RED_300)

    # Called on every scan, and by the light poller below.
    def check_price_alerts(price):
        try:
            hits = []
            with state["alert_lock"]:
                for a in state["alerts"]:
                    if a.get("triggered"): continue
                    if (a["cond"] == "ABOVE" and price >= a["price"]) or (a["cond"] == "BELOW" and price <= a["price"]):
                        a["triggered"], a["triggered_at"], a["triggered_price"] = True, datetime.now().strftime("%d %b %H:%M:%S"), price
                        hits.append(dict(a))
                if hits: save_alerts()
            if not hits: return
            msgs = []
            for a in hits:
                word = "crossed above" if a["cond"] == "ABOVE" else "fell below"
                msgs.append(f"NIFTY {word} {a['price']:,.1f} (now {price:,.1f})" + (f" - {a['label']}" if a.get("label") else ""))
            alert_banner_text.value = "🔔 ALERT: " + "  |  ".join(msgs)
            alert_banner.visible = True
            try: alert_banner.update()
            except Exception: pass
            render_alerts()
            try:
                import winsound  # Windows only; silently skipped elsewhere
                winsound.Beep(1200, 250); winsound.Beep(1600, 250)
            except Exception:
                pass
        except Exception as ex:
            log_glitch("Price Alerts", str(ex))

    # Light poller: lets alerts fire even if Auto Scan is OFF. Only runs while the market is
    # open AND there is at least one active alert; skipped if a scan just ran.
    def alert_poll_worker():
        while state["running"]:
            try:
                has_active = any(not a.get("triggered") for a in list(state["alerts"]))
                recent_scan = (time.time() - state.get("last_scan_ts", 0.0)) < 20
                if has_active and not recent_scan and is_market_open():
                    df = fetch_history("^NSEI", "1d", "1m")
                    if df is not None and not df.empty:
                        p_now = safe_float(df["Close"].iloc[-1])
                        if p_now > 0: check_price_alerts(p_now)
            except Exception as ex:
                log_glitch("Alert Poll", str(ex))
            for _ in range(20):
                if not state["running"]: break
                time.sleep(1)

    notepad_btn = ft.ElevatedButton("📝 Notepad", bgcolor=ft.colors.YELLOW_800, color="white", height=28, on_click=open_notepad)
    alerts_section = ft.Column([
        ft.Row([ft.Text("🔔 PRICE ALERTS", weight=ft.FontWeight.BOLD, color=ft.colors.YELLOW_400, size=11), notepad_btn], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
        ft.Row([alert_price_input, alert_cond_dd, ft.ElevatedButton("Add", bgcolor=ft.colors.YELLOW_800, color="white", height=35, on_click=add_alert)], spacing=4),
        ft.Row([alert_label_input, ft.ElevatedButton("Live price", bgcolor=ft.colors.BLUE_GREY_900, color="white", height=35, on_click=use_live_price)], spacing=4),
        alert_msg_txt,
        ft.Container(content=alerts_list, expand=True, bgcolor="#020409", padding=4, border_radius=6)
    ], expand=True, spacing=4)

    # NOTE (v18.9 mobile): the widgets that used to live in a fixed-width desktop
    # left_panel (Institutional Flow, Risk Manager, Chat Mentor, Price Alerts) are
    # unchanged -- they're just grouped into separate mobile screens further down,
    # instead of one wide side panel.

    # ================= SECTORS WATCH + RADAR (grouped into a mobile screen further down) =================
    ohlc_list = ft.ListView(expand=True, spacing=3, auto_scroll=False)
    def ticker_row(name, ref): return ft.Row([ft.Text(name, size=11, color=ft.colors.WHITE70, weight=ft.FontWeight.BOLD), ref], alignment=ft.MainAxisAlignment.SPACE_BETWEEN)

    sector_bank, sector_it, sector_auto, sector_metal = ft.Text("--", size=11, color=ft.colors.WHITE), ft.Text("--", size=11, color=ft.colors.WHITE), ft.Text("--", size=11, color=ft.colors.WHITE), ft.Text("--", size=11, color=ft.colors.WHITE)
    hdfc_txt, rel_txt, dow_txt, crude_txt = ft.Text("--", size=11, color=ft.colors.WHITE), ft.Text("--", size=11, color=ft.colors.WHITE), ft.Text("--", size=11, color=ft.colors.WHITE), ft.Text("--", size=11, color=ft.colors.WHITE)

    # ================= (formerly CENTER PANEL widgets; unchanged, regrouped into mobile screens below) =================
    time_text = ft.Text("--:--:--", size=12, weight=ft.FontWeight.BOLD, color=ft.colors.CYAN_300)
    dev_list = ft.ListView(expand=True, spacing=5, auto_scroll=True)

    def open_dev_menu(e):
        dev_list.controls.clear()
        if not state["glitch_logs"]: dev_list.controls.append(ft.Text("✅ System Healthy! No glitches found.", color=ft.colors.GREEN_400))
        else: [dev_list.controls.append(ft.Text(log, size=11, color=ft.colors.RED_300)) for log in reversed(state["glitch_logs"])]
        dev_dialog.open = True
        page.update()

    app_title = ft.GestureDetector(on_double_tap=open_dev_menu, content=ft.Text(f"PRO TERMINAL v{APP_VERSION} (DOUBLE-CLICK FOR WATCHDOG)", size=9, color=ft.colors.CYAN_700, weight=ft.FontWeight.BOLD))
    price_text = ft.Text("₹0.00", size=36, weight=ft.FontWeight.BOLD, color=ft.colors.WHITE)
    live_status = ft.Text("Waiting for data...", size=11, color=ft.colors.WHITE54)

    market_status_text = ft.Text("Market status: --", size=10, color=ft.colors.WHITE54)
    last_updated_text = ft.Text("Last updated: --", size=10, color=ft.colors.WHITE54)

    chart_series = ft.LineChartData(data_points=[], stroke_width=2, color=ft.colors.CYAN_400, curved=True, prevent_curve_over_shooting=True)
    line_chart = ft.LineChart(
        data_series=[chart_series], border=ft.border.all(1, ft.colors.WHITE10), expand=True, tooltip_bgcolor=ft.colors.BLUE_GREY_900,
        horizontal_grid_lines=ft.ChartGridLines(interval=10, color=ft.colors.WHITE10, width=1), bottom_axis=ft.ChartAxis(labels=[], labels_size=32)
    )
    chart_last_point_text = ft.Text("Latest point: --", size=10, color=ft.colors.CYAN_200)
    chart_container = ft.Container(
        content=ft.Column([chart_last_point_text, ft.Container(content=line_chart, expand=True)], spacing=4),
        height=200, padding=5, bgcolor="#0A1128", border_radius=10
    )

    sup_text, res_text, vix_text, atr_text, vwap_text = ft.Text("--", size=12, weight=ft.FontWeight.BOLD, color=ft.colors.GREEN_400), ft.Text("--", size=12, weight=ft.FontWeight.BOLD, color=ft.colors.RED_400), ft.Text("--", size=12, weight=ft.FontWeight.BOLD, color=ft.colors.YELLOW_400), ft.Text("--", size=12, weight=ft.FontWeight.BOLD, color=ft.colors.PURPLE_300), ft.Text("--", size=12, weight=ft.FontWeight.BOLD, color=ft.colors.BLUE_300)
    def data_box(title, ref): return ft.Column([ft.Text(title, size=8, color=ft.colors.WHITE54, weight=ft.FontWeight.BOLD), ref], alignment=ft.MainAxisAlignment.CENTER, horizontal_alignment=ft.CrossAxisAlignment.CENTER)
    data_row = ft.Container(content=ft.Row([data_box("S1", sup_text), data_box("R1", res_text), data_box("VIX", vix_text), data_box("ATR (15m)", atr_text), data_box("VWAP", vwap_text)], alignment=ft.MainAxisAlignment.SPACE_EVENLY), bgcolor="#0A1128", padding=10, border_radius=10, border=ft.border.all(1, "#1C2A4A"))

    engine_news_text, engine_tech_text, engine_live_text, engine_4_text = ft.Text("Awaiting Scan...", size=10, color=ft.colors.WHITE70), ft.Text("Awaiting Scan...", size=10, color=ft.colors.WHITE70), ft.Text("Awaiting Scan...", size=10, color=ft.colors.WHITE70), ft.Text("Awaiting Scan...", size=10, color=ft.colors.WHITE70)
    # NOTE (v18.7 fix): a fixed height (not CrossAxisAlignment.STRETCH) is used
    # to keep all 4 engine boxes the same size. STRETCH breaks when the Row
    # sits inside a scrollable/unbounded-height Column (like this center
    # panel), which made the whole panel render blank -- so a fixed height is
    # used instead, with the inner content scrollable in case text overflows.
    def engine_box(title, icon, icon_color, ref):
        return ft.Container(
            expand=True, height=130, padding=8, border_radius=8, bgcolor="#0A1128",
            border=ft.border.only(left=ft.border.BorderSide(3, icon_color)),
            content=ft.Column([
                ft.Row([ft.Icon(icon, size=14, color=icon_color), ft.Text(title, size=9, weight=ft.FontWeight.BOLD, color=icon_color)]),
                ft.Column([ref], scroll=ft.ScrollMode.AUTO, expand=True)
            ], spacing=2)
        )
    box_news, box_tech, box_live, box_engine4 = engine_box("ENGINE 1: MACRO SENTIMENT", ft.icons.PUBLIC, ft.colors.ORANGE_400, engine_news_text), engine_box("ENGINE 2: QUANT & VIX", ft.icons.DATA_EXPLORATION, ft.colors.PURPLE_400, engine_tech_text), engine_box("ENGINE 3: PRICE ACTION", ft.icons.BOLT, ft.colors.YELLOW_400, engine_live_text), engine_box("ENGINE 4: OPTIONS LOGIC", ft.icons.ANCHOR, ft.colors.CYAN_400, engine_4_text)

    final_verdict_text = ft.Text("RUN LIVE SCAN TO GENERATE SETUP", size=12, weight=ft.FontWeight.W_900, color=ft.colors.WHITE)
    entry_text, target_text, sl_text, reason_text = ft.Text("ENTRY: --", size=11, weight=ft.FontWeight.BOLD, color=ft.colors.WHITE), ft.Text("TARGET: --", size=11, weight=ft.FontWeight.BOLD, color=ft.colors.GREEN_300), ft.Text("SL: --", size=11, weight=ft.FontWeight.BOLD, color=ft.colors.RED_300), ft.Text("REASON: Awaiting market scan...", size=10, color=ft.colors.CYAN_200, italic=True)
    target2_text = ft.Text("", size=11, weight=ft.FontWeight.BOLD, color=ft.colors.GREEN_300)
    rr_text = ft.Text("R:R: --", size=10, color=ft.colors.WHITE54)
    sr_text = ft.Text("SUPPORT: --    |    RESISTANCE: --", size=11, weight=ft.FontWeight.BOLD, color=ft.colors.CYAN_200)
    wait_call_text = ft.Text("", size=10, color=ft.colors.GREEN_300)
    wait_put_text = ft.Text("", size=10, color=ft.colors.RED_300)
    final_box = ft.Container(content=ft.Column([
        final_verdict_text, ft.Divider(color=ft.colors.WHITE24, height=6),
        ft.Row([entry_text, target_text, target2_text, sl_text], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
        rr_text, ft.Divider(color=ft.colors.WHITE24, height=6),
        sr_text, wait_call_text, wait_put_text,
        ft.Divider(color=ft.colors.WHITE24, height=6), reason_text
    ], horizontal_alignment=ft.CrossAxisAlignment.CENTER, spacing=3), bgcolor="#070C1E", padding=12, border_radius=10, border=ft.border.all(2, ft.colors.BLUE_700))

    # v18.8: fills the verdict box. With an active signal -> full plan. Without one ->
    # the exact CALL / PUT trigger levels the app's own rules are waiting for.
    def render_trade_plan(plan, price, anchor, vwap_val, atr, levels):
        below, above = nearby_levels(price, levels)
        lo, hi = fmt_levels(below, levels), fmt_levels(above, levels)
        sr_text.value = f"SUPPORT: {lo}    |    RESISTANCE: {hi}" + ("   (* = round number)" if "*" in lo + hi else "")
        if plan:
            e = plan["entry"]
            entry_text.value = f"ENTRY: {e:.0f}"
            target_text.value = f"TARGET 1: {plan['t1']:.0f} ({plan['t1'] - e:+.0f})"
            target2_text.value = f"TARGET 2: {plan['t2']:.0f} ({plan['t2'] - e:+.0f})"
            sl_text.value = f"STOPLOSS: {plan['sl']:.0f} ({plan['sl'] - e:+.0f})"
            note = f" | T1 capped near level {plan['capped_by']:.0f}" if plan["capped_by"] else ""
            warn = "  ⚠️ Poor R:R - better to skip" if plan["quality"] == "Poor" else ""
            rr_text.value = f"R:R 1:{plan['rr']:.1f} ({plan['quality']}){note}{warn}"
            rr_text.color = ft.colors.GREEN_300 if plan["quality"] == "Good" else ft.colors.YELLOW_300 if plan["quality"] == "OK" else ft.colors.RED_300
            wait_call_text.value = ""; wait_put_text.value = ""
        else:
            entry_text.value = "ENTRY: wait for trigger"
            target_text.value, target2_text.value, sl_text.value = "TARGET: --", "", "STOPLOSS: --"
            ce_trig, pe_trig = max(anchor + 20, vwap_val), min(anchor - 20, vwap_val)
            pc = build_trade_plan("LONG", ce_trig, atr, levels)
            pp = build_trade_plan("SHORT", pe_trig, atr, levels)
            rr_text.value = "No active signal - levels to wait for:"
            rr_text.color = ft.colors.WHITE54
            wait_call_text.value = f"▲ CALL above {ce_trig:.0f}:  T1 {pc['t1']:.0f} | T2 {pc['t2']:.0f} | SL {pc['sl']:.0f}   (R:R 1:{pc['rr']:.1f})"
            wait_put_text.value = f"▼ PUT below {pe_trig:.0f}:  T1 {pp['t1']:.0f} | T2 {pp['t2']:.0f} | SL {pp['sl']:.0f}   (R:R 1:{pp['rr']:.1f})"

    live_news_ticker = ft.Text("Fetching real-time macro headlines...", size=11, color=ft.colors.ORANGE_300, weight=ft.FontWeight.BOLD, max_lines=2, overflow=ft.TextOverflow.ELLIPSIS)
    news_ticker_box = ft.Container(content=ft.Row([ft.Icon(ft.icons.NEWSPAPER, color=ft.colors.ORANGE_400, size=16), live_news_ticker]), bgcolor="#0A1128", padding=8, border_radius=8, border=ft.border.all(1, ft.colors.ORANGE_700))

    # ================= MANUAL MARKET ANALYSIS PANEL (v18.4 base + v18.5 upgrades) =================
    manual_price_input = ft.TextField(label="Manual Price", width=120, height=35, text_size=11, content_padding=5, keyboard_type=ft.KeyboardType.NUMBER)
    manual_date_input = ft.TextField(label="Date (YYYY-MM-DD)", width=130, height=35, text_size=10, content_padding=5)
    manual_time_input = ft.TextField(label="Time (HH:MM)", width=90, height=35, text_size=10, content_padding=5)
    manual_result_text = ft.Text("Enter a price + date/time and click ANALYZE.", size=11, color=ft.colors.WHITE70)
    manual_history_list = ft.ListView(height=120, spacing=3, auto_scroll=False)
    manual_accuracy_text = ft.Text("Manual Engine Accuracy: gathering data (0 verified)", size=9, color=ft.colors.WHITE54)

    def fill_now(e):
        now = datetime.now()
        manual_date_input.value = now.strftime("%Y-%m-%d")
        manual_time_input.value = now.strftime("%H:%M")
        manual_date_input.update(); manual_time_input.update()

    # ---- NEW: rule-based diagnosis for a wrong prediction ----
    # This explains WHICH signals conflicted at entry time -- it cannot
    # know the true real-world cause (news, FII flow, global cues, etc.),
    # only what the app's own engines were saying at that moment.
    def generate_diagnosis(p):
        reasons = []
        verdict_core = p["verdict"].split(" ")[0]
        if p["bull_count"] == p["bear_count"]:
            reasons.append("Signals were tied/conflicting at entry (no clear majority).")
        if p.get("e4_zone") and "EXTREME" in p["e4_zone"]:
            reasons.append("Entry was inside an EXTREME zone (high risk, far from anchor).")
        if p["macro"] not in ("NEUTRAL",) and p["macro"] != verdict_core:
            reasons.append(f"News macro ({p['macro']}) conflicted with the verdict.")
        if p["e4_bias"] not in ("NEUTRAL",) and p["e4_bias"] != verdict_core:
            reasons.append(f"Engine 4 bias ({p['e4_bias']}) disagreed with the verdict.")
        if not reasons:
            reasons.append("Signals were aligned, but the market still moved the other way -- likely a news-driven or random move outside the model's scope.")
        return " | ".join(reasons)

    # ---- NEW: multi-timeframe confirmation (Improvement #6) ----
    # Runs in a background thread so the instant verdict isn't delayed.
    def compute_mtf_confirmation(verdict):
        verdict_core = verdict.split(" ")[0]
        agree, total, tf_notes = 0, 0, []
        for interval, label in [("5m", "5-Min"), ("15m", "15-Min")]:
            try:
                df = fetch_history("^NSEI", "5d", interval)
                if df is None or df.empty or len(df) < 6:
                    tf_notes.append(f"{label}: data unavailable")
                    continue
                recent_close = safe_float(df["Close"].iloc[-1])
                ref_close = safe_float(df["Close"].iloc[-6])
                tf_trend = "BULLISH" if recent_close >= ref_close else "BEARISH"
                total += 1
                if tf_trend == verdict_core:
                    agree += 1
                    tf_notes.append(f"{label}: {tf_trend} \u2713 agrees")
                else:
                    tf_notes.append(f"{label}: {tf_trend} \u2717 disagrees")
            except Exception:
                tf_notes.append(f"{label}: error fetching")
        header = f"MTF Confirmation ({agree}/{total} agree):" if total else "MTF Confirmation: unavailable"
        return header + "\n" + "\n".join(tf_notes)

    def refresh_prediction_history():
        try:
            manual_history_list.controls.clear()
            if not state["predictions"]:
                manual_history_list.controls.append(ft.Text("No manual predictions yet.", size=9, color=ft.colors.WHITE54))
            for p in reversed(state["predictions"][-30:]):
                if p.get("verified") and str(p.get("verdict", "")).split(" ")[0] not in ("BULLISH", "BEARISH"):
                    icon, color = "➖", ft.colors.WHITE54
                    txt = f"{icon} [{p['pred_date']} {p['pred_time']}] ₹{p['price']:.1f} → {p['verdict']} (no-trade call, not scored | market went {p['actual_trend']})"
                elif p.get("verified"):
                    icon = "✅" if p["correct"] else "❌"
                    color = ft.colors.GREEN_400 if p["correct"] else ft.colors.RED_400
                    extra = f" | {p['diagnosis']}" if p.get("diagnosis") else ""
                    method_note = f" [{p['verify_method']}]" if p.get("verify_method") else ""
                    txt = f"{icon} [{p['pred_date']} {p['pred_time']}] ₹{p['price']:.1f} → {p['verdict']} (Actual: {p['actual_trend']}){method_note}{extra}"
                else:
                    icon, color = "⏳", ft.colors.WHITE54
                    txt = f"{icon} [{p['pred_date']} {p['pred_time']}] ₹{p['price']:.1f} → {p['verdict']} (pending verification)"
                manual_history_list.controls.append(ft.Text(txt, size=9, color=color))
            manual_history_list.update()
        except Exception as ex:
            log_glitch("Prediction History UI", str(ex))

    # ---- v18.8: accuracy-based auto-tuning ----
    # Looks at the last 20 VERIFIED directional calls (BULLISH/BEARISH). "No trade" calls are
    # abstentions, so they are not scored. Based on that hit-rate it raises the minimum
    # confidence a directional verdict must have (else it is downgraded to NO TRADE).
    # Numeric threshold only -- nothing rewrites the app's logic.
    def get_adaptive_mode():
        scored = [p for p in list(state["predictions"]) if p.get("verified") and str(p.get("verdict", "")).split(" ")[0] in ("BULLISH", "BEARISH")]
        scored.sort(key=lambda p: (p.get("pred_date", ""), p.get("pred_time", "")))
        recent = scored[-20:]
        n = len(recent)
        if n < 5: return 0, "Learning", None, n
        acc = sum(1 for p in recent if p.get("correct")) / n * 100
        if acc >= 60: return 0, "Normal", acc, n
        if acc >= 45: return 55, "Cautious", acc, n
        return 70, "Strict", acc, n

    def update_manual_accuracy_banner():
        try:
            min_conf, mode, acc, n = get_adaptive_mode()
            if acc is None:
                manual_accuracy_text.value = f"Manual Engine: learning - {n}/5 scored calls needed before auto-tuning starts"
                manual_accuracy_text.color = ft.colors.WHITE54
            else:
                manual_accuracy_text.value = f"Manual Engine Accuracy: {acc:.0f}% ({n} scored) | Mode: {mode}" + (f" - min confidence {min_conf}%" if min_conf else "")
                manual_accuracy_text.color = ft.colors.GREEN_400 if mode == "Normal" else ft.colors.YELLOW_400 if mode == "Cautious" else ft.colors.RED_400
            manual_accuracy_text.update()
        except Exception as ex:
            log_glitch("Accuracy Banner", str(ex))

    # ---- Improvement #5, #7, #8 + prediction save ----
    def run_manual_analysis(e):
        try:
            raw = (manual_price_input.value or "").strip()
            manual_price = safe_float(raw, -1.0)
            if manual_price <= 0:
                manual_result_text.value = "⚠️ Enter a valid positive price."
                manual_result_text.color = ft.colors.RED_300
                manual_result_text.update()
                return

            date_str = (manual_date_input.value or "").strip() or datetime.now().strftime("%Y-%m-%d")
            time_str = (manual_time_input.value or "").strip() or datetime.now().strftime("%H:%M")
            try:
                pred_dt = datetime.strptime(f"{date_str} {time_str}", "%Y-%m-%d %H:%M")
            except Exception:
                manual_result_text.value = "⚠️ Date/Time format galat hai. Use YYYY-MM-DD and HH:MM."
                manual_result_text.color = ft.colors.RED_300
                manual_result_text.update()
                return

            vwap = state["vwap"] if state["vwap"] > 0 else manual_price
            anchor = state["anchor"] if state["anchor"] > 0 else manual_price
            macro = state["macro"]
            atr_val = state.get("atr", 0.0)
            vol_change = state.get("volume_change_pct", 0.0)

            trend = "BULLISH" if manual_price >= vwap else "BEARISH"
            e4_bias, e4_state, e4_strike, e4_opt, e4_zone = calculate_engine_4(manual_price, anchor)

            # Improvement #5: confidence-weighted verdict (Engine 4 weighted
            # highest since it's price-structure based, News lowest since it's
            # just keyword matching)
            weights = {"trend": 1.5, "e4": 2.0, "macro": 1.0}
            bull_score = (weights["trend"] if trend == "BULLISH" else 0) + (weights["e4"] if e4_bias == "BULLISH" else 0) + (weights["macro"] if macro == "BULLISH" else 0)
            bear_score = (weights["trend"] if trend == "BEARISH" else 0) + (weights["e4"] if e4_bias == "BEARISH" else 0) + (weights["macro"] if macro == "BEARISH" else 0)
            total_weight = sum(weights.values())
            if bull_score > bear_score:
                verdict, v_color, confidence = "BULLISH", ft.colors.GREEN_400, (bull_score / total_weight) * 100
            elif bear_score > bull_score:
                verdict, v_color, confidence = "BEARISH", ft.colors.RED_400, (bear_score / total_weight) * 100
            else:
                verdict, v_color, confidence = "SIDEWAYS / NO TRADE ZONE", ft.colors.YELLOW_400, 50.0

            # v18.8: accuracy-based auto-tuning of the minimum confidence
            raw_verdict = verdict
            min_conf, tune_mode, tune_acc, tune_n = get_adaptive_mode()
            tune_note = ""
            if verdict in ("BULLISH", "BEARISH") and confidence < min_conf:
                tune_note = f"Auto-tune ({tune_mode}, accuracy {tune_acc:.0f}%): confidence {confidence:.0f}% < required {min_conf}% -> NO TRADE\n"
                verdict, v_color = "SIDEWAYS / NO TRADE ZONE", ft.colors.YELLOW_400

            # v18.8: Entry / Targets / SL / Support-Resistance (same logic as the main verdict box).
            # The old note used 0.35 x ATR target vs 1.5 x ATR stop, i.e. it always said "Poor".
            levels = state.get("levels", [])
            if atr_val > 0 and levels and raw_verdict in ("BULLISH", "BEARISH"):
                plan = build_trade_plan("LONG" if raw_verdict == "BULLISH" else "SHORT", manual_price, max(atr_val, manual_price * 0.0005), levels)
                below, above = nearby_levels(manual_price, levels)
                lvtxt = lambda lst: fmt_levels(lst, levels)
                prefix = "Plan" if verdict == raw_verdict else "Plan (only if you still take it)"
                cap = f" | T1 capped near {plan['capped_by']:.0f}" if plan["capped_by"] else ""
                rr_note = (f"{prefix}: Entry {manual_price:.0f} | T1 {plan['t1']:.0f} | T2 {plan['t2']:.0f} | SL {plan['sl']:.0f}\n"
                           f"R:R 1:{plan['rr']:.1f} ({plan['quality']}){cap}\n"
                           f"Support {lvtxt(below)} | Resistance {lvtxt(above)}  (levels from last LIVE SCAN)")
            else:
                rr_note = "Trade plan: needs a directional verdict and one LIVE SCAN (for ATR & levels)"

            # Improvement #8: volume-confirmed breakout
            if "BREAKOUT" in e4_state or "BREAKDOWN" in e4_state:
                if (e4_bias == "BULLISH" and vol_change >= 25) or (e4_bias == "BEARISH" and vol_change <= -25):
                    vol_note = f"Volume Confirmed ({vol_change:+.0f}%)"
                else:
                    vol_note = f"Volume NOT confirming breakout ({vol_change:+.0f}%) — weak signal"
            else:
                vol_note = "No breakout/breakdown in progress"

            bull_count = [trend, e4_bias, macro].count("BULLISH")
            bear_count = [trend, e4_bias, macro].count("BEARISH")

            manual_result_text.value = (
                f"VERDICT: {verdict}  (Confidence: {confidence:.0f}%)\n"
                f"{tune_note}"
                f"For: {pred_dt.strftime('%d %b %Y, %H:%M')}\n"
                f"VWAP Trend: {trend}  (Price ₹{manual_price:.1f} vs VWAP ₹{vwap:.1f})\n"
                f"Engine 4: {e4_bias} | {e4_state}\n"
                f"Zone: {e4_zone} | Suggested Strike: {e4_strike} {e4_opt}\n"
                f"News Macro: {macro}\n"
                f"{rr_note}\n"
                f"{vol_note}\n"
                f"Checking multi-timeframe confirmation..."
            )
            manual_result_text.color = v_color
            manual_result_text.update()

            pred_record = {
                "id": pred_dt.strftime("%Y%m%d%H%M%S") + f"_{random.randint(100, 999)}",
                "pred_date": date_str, "pred_time": time_str,
                "entered_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "price": manual_price, "vwap": vwap, "anchor": anchor, "macro": macro,
                "verdict": verdict, "raw_verdict": raw_verdict, "min_conf": min_conf, "e4_bias": e4_bias, "e4_zone": e4_zone,
                "bull_count": bull_count, "bear_count": bear_count,
                "verified": False, "actual_price": None, "actual_trend": None,
                "correct": None, "diagnosis": None
            }
            with state["pred_lock"]:
                state["predictions"].append(pred_record)
                save_predictions()
            refresh_prediction_history()

            # Improvement #6 continued: fetch MTF data in background, then patch the result text
            def mtf_worker():
                try:
                    mtf_note = compute_mtf_confirmation(raw_verdict)
                except Exception as ex:
                    log_glitch("MTF Check", str(ex))
                    mtf_note = "Multi-timeframe check unavailable."
                try:
                    manual_result_text.value = manual_result_text.value.replace(
                        "Checking multi-timeframe confirmation...", mtf_note)
                    manual_result_text.update()
                except Exception as ex:
                    log_glitch("MTF UI", str(ex))

            threading.Thread(target=mtf_worker, daemon=True).start()

        except Exception as ex:
            log_glitch("Manual Analysis", str(ex))
            manual_result_text.value = f"Error: {ex}"
            manual_result_text.color = ft.colors.RED_400
            try: manual_result_text.update()
            except: pass

    # ---- NEW: verification against actual market data ----
    # NOTE (limitation): free yfinance intraday (1m/5m) history only
    # covers the last several days, so verifying anything older reliably
    # needs a daily-level benchmark. This checks the NEXT TRADING DAY's
    # close against your entered price -- a simplification, not a perfect
    # intraday replay. Predictions younger than 30 minutes are skipped
    # (market hasn't had time to move / next close isn't out yet).
    def verify_predictions():
        try:
            with state["pred_lock"]:
                pending = [p for p in state["predictions"] if not p.get("verified")]
            if not pending:
                return 0

            # Fast path: try recent (~last 7 days) 1-minute data first, so a
            # same-day prediction can verify ~30 min later instead of having
            # to wait for tomorrow's close.
            intraday_df = None
            try:
                intraday_df = fetch_history("^NSEI", "7d", "1m")
            except Exception as ex:
                log_glitch("Verify Predictions (intraday fetch)", str(ex))

            daily_df = None  # fetched lazily only if a prediction actually needs the fallback

            verified_count = 0
            with state["pred_lock"]:
                for p in state["predictions"]:
                    if p.get("verified"):
                        continue
                    try:
                        pred_dt = datetime.strptime(f"{p['pred_date']} {p['pred_time']}", "%Y-%m-%d %H:%M")
                    except Exception:
                        continue
                    if pred_dt >= datetime.now() - timedelta(minutes=30):
                        continue  # too recent either way -- market hasn't had time to move yet

                    actual_price, method = None, None

                    if intraday_df is not None and not intraday_df.empty:
                        try:
                            idx = intraday_df.index
                            idx_naive = idx.tz_localize(None) if idx.tz is not None else idx
                            if idx_naive.min() <= pred_dt <= idx_naive.max():
                                target_dt = pred_dt + timedelta(minutes=30)
                                nearest_pos = int(abs(idx_naive - target_dt).argmin())
                                actual_price = safe_float(intraday_df["Close"].iloc[nearest_pos])
                                method = "intraday (~30 min later)"
                        except Exception as ex:
                            log_glitch("Verify Predictions (intraday match)", str(ex))

                    if actual_price is None:
                        if daily_df is None:
                            daily_df = fetch_history("^NSEI", "2y", "1d")
                        if daily_df is None or daily_df.empty:
                            continue
                        future_rows = daily_df[daily_df.index.date > pred_dt.date()]
                        if future_rows.empty:
                            continue
                        actual_price = safe_float(future_rows["Close"].iloc[0])
                        method = "next trading day's close"

                    diff = actual_price - p["price"]
                    atr_ref = max(state.get("atr", 20.0), 5.0)
                    if abs(diff) < atr_ref * 0.3:
                        actual_trend = "NEUTRAL"
                    else:
                        actual_trend = "BULLISH" if diff > 0 else "BEARISH"

                    verdict_core = p["verdict"].split(" ")[0]
                    if verdict_core == "SIDEWAYS":
                        correct = (actual_trend == "NEUTRAL")
                    else:
                        correct = (actual_trend == verdict_core)

                    p["verified"] = True
                    p["actual_price"] = actual_price
                    p["actual_trend"] = actual_trend
                    p["correct"] = correct
                    p["verify_method"] = method
                    p["diagnosis"] = None if correct else generate_diagnosis(p)
                    verified_count += 1
                if verified_count:
                    save_predictions()
            return verified_count
        except Exception as ex:
            log_glitch("Verify Predictions", str(ex))
            return 0

    def on_verify_click(e):
        def worker():
            n = verify_predictions()
            refresh_prediction_history()
            update_manual_accuracy_banner()
            try: page.update()
            except: pass
        threading.Thread(target=worker, daemon=True).start()

    verify_btn = ft.ElevatedButton("🔍 Verify Past Predictions", bgcolor=ft.colors.BLUE_GREY_900, color="white", height=30, on_click=on_verify_click)

    manual_analysis_box = ft.Container(
        bgcolor="#0A1128", padding=12, border_radius=10, border=ft.border.all(1, ft.colors.TEAL_700),
        content=ft.Column([
            ft.Row([ft.Icon(ft.icons.CALCULATE, color=ft.colors.TEAL_300, size=14), ft.Text("MANUAL MARKET ANALYSIS", weight=ft.FontWeight.BOLD, color=ft.colors.TEAL_300, size=11)]),
            manual_accuracy_text,
            ft.Row([manual_price_input, manual_date_input, manual_time_input, ft.IconButton(ft.icons.SCHEDULE, tooltip="Fill current date/time", icon_color=ft.colors.TEAL_300, on_click=fill_now)], spacing=6, wrap=True),
            ft.Row([ft.ElevatedButton("ANALYZE", bgcolor=ft.colors.TEAL_700, color="white", height=35, on_click=run_manual_analysis), verify_btn], spacing=6),
            ft.Container(content=manual_result_text, bgcolor="#020409", padding=8, border_radius=6),
            ft.Text("History:", size=9, color=ft.colors.WHITE54),
            ft.Container(content=manual_history_list, bgcolor="#020409", padding=4, border_radius=6)
        ], spacing=6)
    )

    # ================= TRADE HISTORY (LEDGER) DIALOG =================
    ledger_dialog = ft.AlertDialog(title=ft.Text("PAPER TRADE HISTORY (LEDGER)", color=ft.colors.CYAN_400, weight=ft.FontWeight.BOLD), content=ft.Container(width=320, height=400, bgcolor=ft.colors.BLACK87, padding=10), actions=[])
    ledger_list = ft.ListView(expand=True, spacing=5, auto_scroll=True)
    ledger_dialog.content.content = ledger_list
    page.overlay.append(ledger_dialog)

    def open_ledger(e):
        ledger_list.controls.clear()
        try:
            if os.path.exists("nifty_trade_journal.csv"):
                with open("nifty_trade_journal.csv", "r", encoding="utf-8") as f:
                    reader = csv.reader(f)
                    header = next(reader, None)
                    if header:
                        ledger_list.controls.append(ft.Row([ft.Text(h, size=10, weight=ft.FontWeight.BOLD, color=ft.colors.WHITE54, expand=1) for h in header]))
                        ledger_list.controls.append(ft.Divider(color=ft.colors.WHITE24, height=2))
                        for row in reversed(list(reader)):
                            try:
                                pnl = float(row[5])
                                color = ft.colors.GREEN_400 if pnl >= 0 else ft.colors.RED_400
                                row_controls = [ft.Text(str(val), size=10, color=color if i == 5 else ft.colors.WHITE, expand=1) for i, val in enumerate(row)]
                                ledger_list.controls.append(ft.Row(row_controls))
                            except Exception as row_ex:
                                log_glitch("Ledger Row", str(row_ex))
                                continue
            else: ledger_list.controls.append(ft.Text("No paper trades taken yet. Execute a trade to see ledger.", color=ft.colors.WHITE54))
        except Exception as ex:
            log_glitch("Ledger Load", str(ex))
            ledger_list.controls.append(ft.Text(f"Error loading ledger: {ex}", color=ft.colors.RED_400))
        ledger_dialog.open = True
        page.update()

    # ================= PAPER TRADING UI (Option Chain + multi-position, v18.7) =================
    MAX_OPEN_POSITIONS = 3

    def update_lots(delta):
        state["order_lots"] = max(1, state["order_lots"] + delta)
        lot_val_txt.value = str(state["order_lots"])
        try: lot_val_txt.update()
        except: pass

    ledger_btn = ft.ElevatedButton("📜 TRADE HISTORY", bgcolor=ft.colors.BLUE_GREY_900, color="white", height=30, on_click=open_ledger)
    lot_val_txt = ft.Text("1", weight=ft.FontWeight.BOLD, size=14)
    target_input = ft.TextField(label="Target (₹)", width=70, height=35, text_size=10, content_padding=5, text_align=ft.TextAlign.CENTER)
    sl_input = ft.TextField(label="StopLoss (₹)", width=70, height=35, text_size=10, content_padding=5, text_align=ft.TextAlign.CENTER)
    order_message_txt = ft.Text("Select a strike below and hit Buy CE/PE to enter a paper trade.", size=10, color=ft.colors.WHITE54)
    positions_count_txt = ft.Text(f"Open Positions: 0/{MAX_OPEN_POSITIONS}", size=10, color=ft.colors.WHITE54)
    avail_fund_txt = ft.Text("Available: ₹100000.00 | Used Margin: ₹0.00", size=11, color=ft.colors.WHITE54)
    capital_text = ft.Text("Capital: ₹100000.00", size=10, color=ft.colors.CYAN_400)
    stats_text = ft.Text("Trades: 0 | Peak Cap: ₹100k | Max DD: 0%", size=9, color=ft.colors.WHITE54)
    total_pnl_text = ft.Text("Total P&L: ₹0.00", size=14, weight=ft.FontWeight.BOLD, color=ft.colors.WHITE)
    positions_list = ft.Column(spacing=4)

    option_chain_header = ft.Row([
        ft.Text("CE LTP", size=9, color=ft.colors.BLUE_300, weight=ft.FontWeight.BOLD, width=68, text_align=ft.TextAlign.CENTER),
        ft.Text("BUY", size=9, color=ft.colors.WHITE38, width=48, text_align=ft.TextAlign.CENTER),
        ft.Text("STRIKE", size=9, color=ft.colors.YELLOW_300, weight=ft.FontWeight.BOLD, width=70, text_align=ft.TextAlign.CENTER),
        ft.Text("BUY", size=9, color=ft.colors.WHITE38, width=48, text_align=ft.TextAlign.CENTER),
        ft.Text("PE LTP", size=9, color=ft.colors.RED_300, weight=ft.FontWeight.BOLD, width=68, text_align=ft.TextAlign.CENTER),
    ], alignment=ft.MainAxisAlignment.CENTER)
    option_chain_list = ft.Column(spacing=3, controls=[ft.Text("Run a Live Scan to load the option chain.", size=9, color=ft.colors.WHITE54)])

    def refresh_positions_ui():
        try:
            positions_list.controls.clear()
            if not state["positions"]:
                positions_list.controls.append(ft.Text("No open positions.", size=10, color=ft.colors.WHITE54))
            for pos in state["positions"]:
                pnl_color = ft.colors.GREEN_400 if pos["pnl"] >= 0 else ft.colors.RED_400
                positions_list.controls.append(
                    ft.Container(
                        bgcolor="#070C1E", padding=6, border_radius=6, border=ft.border.all(1, ft.colors.WHITE10),
                        content=ft.Row([
                            ft.Column([
                                ft.Text(pos["symbol"], size=11, weight=ft.FontWeight.BOLD, color=ft.colors.WHITE),
                                ft.Text(f"Qty {pos['qty']} | Buy ₹{pos['buy_price']:.2f} | LTP ₹{pos['curr_ltp']:.2f} | Entry {pos['entry_time']}", size=9, color=ft.colors.WHITE54)
                            ], expand=True, spacing=2),
                            ft.Column([
                                ft.Text(f"{'+' if pos['pnl'] >= 0 else ''}₹{pos['pnl']:.2f}", size=13, weight=ft.FontWeight.BOLD, color=pnl_color),
                                ft.ElevatedButton("Exit", bgcolor=ft.colors.RED_700, color="white", height=26, on_click=make_exit_handler(pos["id"]))
                            ], horizontal_alignment=ft.CrossAxisAlignment.END, spacing=2)
                        ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN)
                    )
                )
            total_pnl = sum(p["pnl"] for p in state["positions"])
            total_pnl_text.value = f"Total P&L: {'+' if total_pnl >= 0 else ''}₹{total_pnl:.2f}"
            total_pnl_text.color = ft.colors.GREEN_400 if total_pnl >= 0 else ft.colors.RED_400
            # v19.0 mobile: keep the always-visible top-bar P&L badge in sync too
            if state["positions"]:
                top_pnl_badge.value = f"P&L: {'+' if total_pnl >= 0 else ''}₹{total_pnl:.2f}"
                top_pnl_badge.color = ft.colors.GREEN_400 if total_pnl >= 0 else ft.colors.RED_400
            else:
                top_pnl_badge.value = ""
            try: top_pnl_badge.update()
            except: pass
            used_margin = sum(p["buy_price"] * p["qty"] for p in state["positions"])
            avail_fund_txt.value = f"Available: ₹{(state['capital'] - used_margin):.2f} | Used Margin: ₹{used_margin:.2f}"
            positions_count_txt.value = f"Open Positions: {len(state['positions'])}/{MAX_OPEN_POSITIONS}"
            # v18.9: mirror total P&L into the always-visible top bar so it's seen on every screen
            top_pnl_text.visible = bool(state["positions"])
            if state["positions"]:
                top_pnl_text.value = f"P&L: {'+' if total_pnl >= 0 else ''}\u20b9{total_pnl:.0f}"
                top_pnl_text.color = ft.colors.GREEN_400 if total_pnl >= 0 else ft.colors.RED_400
            try:
                positions_list.update(); total_pnl_text.update(); avail_fund_txt.update(); positions_count_txt.update()
                top_pnl_text.update()
            except: pass
        except Exception as ex:
            log_glitch("Positions UI", str(ex))

    def refresh_option_chain():
        try:
            option_chain_list.controls.clear()
            atm = state.get("atm_strike", 0)
            if atm <= 0 or state["price"] <= 0:
                option_chain_list.controls.append(ft.Text("Run a Live Scan to load the option chain.", size=9, color=ft.colors.WHITE54))
                try: option_chain_list.update()
                except: pass
                return
            strikes = [atm + i * 50 for i in range(-3, 4)]
            chain = {}
            for strike in strikes:
                ce_p = get_simulated_option_ltp(state["price"], strike, "CE", state["vix"])
                pe_p = get_simulated_option_ltp(state["price"], strike, "PE", state["vix"])
                chain[strike] = {"ce": ce_p, "pe": pe_p}
                is_atm = (strike == atm)
                row = ft.Container(
                    bgcolor="#0F1B3A" if is_atm else "#020409", padding=4, border_radius=4,
                    content=ft.Row([
                        ft.Text(f"₹{ce_p:.2f}", size=10, color=ft.colors.BLUE_300, width=68, text_align=ft.TextAlign.CENTER),
                        ft.ElevatedButton("Buy", bgcolor=ft.colors.BLUE_700, color="white", height=26, width=48, on_click=make_buy_handler(strike, "CE")),
                        ft.Text(f"{strike}" + (" ★" if is_atm else ""), size=10, color=ft.colors.YELLOW_300 if is_atm else ft.colors.WHITE, weight=ft.FontWeight.BOLD, width=70, text_align=ft.TextAlign.CENTER),
                        ft.ElevatedButton("Buy", bgcolor=ft.colors.RED_700, color="white", height=26, width=48, on_click=make_buy_handler(strike, "PE")),
                        ft.Text(f"₹{pe_p:.2f}", size=10, color=ft.colors.RED_300, width=68, text_align=ft.TextAlign.CENTER),
                    ], alignment=ft.MainAxisAlignment.CENTER)
                )
                option_chain_list.controls.append(row)
            state["chain"] = chain
            try: option_chain_list.update()
            except: pass
        except Exception as ex:
            log_glitch("Option Chain UI", str(ex))

    def place_order(strike, side):
        if not is_market_open():
            order_message_txt.value = "⚠️ Market is CLOSED — new paper trades allowed only 9:15–15:30 IST, Mon-Fri. (Existing positions can still be exited anytime.)"
            order_message_txt.color = ft.colors.RED_300
            try: order_message_txt.update()
            except: pass
            return
        if state["price"] <= 0:
            order_message_txt.value = "⚠️ Run a Live Scan first."
            order_message_txt.color = ft.colors.RED_300
            try: order_message_txt.update()
            except: pass
            return

        with state["trade_lock"]:
            if len(state["positions"]) >= MAX_OPEN_POSITIONS:
                order_message_txt.value = f"⚠️ Max {MAX_OPEN_POSITIONS} open positions reached. Exit one to add more."
                order_message_txt.color = ft.colors.RED_300
                try: order_message_txt.update()
                except: pass
                return

            live_p = get_simulated_option_ltp(state["price"], strike, side, state["vix"])
            qty = state["order_lots"] * 50
            req_marg = live_p * qty
            used_margin = sum(p["buy_price"] * p["qty"] for p in state["positions"])
            if live_p <= 0 or (used_margin + req_marg) > state["capital"]:
                order_message_txt.value = "⚠️ Insufficient margin for this order."
                order_message_txt.color = ft.colors.RED_300
                try: order_message_txt.update()
                except: pass
                return

            position = {
                "id": datetime.now().strftime("%H%M%S") + f"_{random.randint(100, 999)}",
                "symbol": f"NIFTY {strike} {side}", "side": side, "strike": strike,
                "qty": qty, "buy_price": live_p, "curr_ltp": live_p, "pnl": 0.0,
                "sl_val": safe_float(sl_input.value, 0.0), "target_val": safe_float(target_input.value, 0.0),
                "entry_time": datetime.now().strftime("%H:%M:%S")
            }
            state["positions"].append(position)
            order_message_txt.value = f"✅ Bought {position['symbol']} x{qty} @ ₹{live_p:.2f}"
            order_message_txt.color = ft.colors.GREEN_400

        try: order_message_txt.update()
        except: pass
        refresh_positions_ui()

    def square_off_position(pos_id):
        with state["trade_lock"]:
            pos = next((p for p in state["positions"] if p["id"] == pos_id), None)
            if not pos:
                return
            pnl = pos["pnl"]
            state["capital"] += pnl; state["trade_count"] += 1
            if pnl >= 0: state["wins"] += 1; state["current_streak"] = state["current_streak"] + 1 if state["current_streak"] >= 0 else 1
            else: state["losses"] += 1; state["current_streak"] = state["current_streak"] - 1 if state["current_streak"] <= 0 else -1

            if state["capital"] > state["peak_capital"]: state["peak_capital"] = state["capital"]
            dd = ((state["peak_capital"] - state["capital"]) / state["peak_capital"]) * 100
            if dd > state["max_drawdown_pct"]: state["max_drawdown_pct"] = dd

            try:
                exists = os.path.exists("nifty_trade_journal.csv")
                with open("nifty_trade_journal.csv", "a", newline="", encoding="utf-8") as f:
                    w = csv.writer(f)
                    if not exists: w.writerow(["Time", "Symbol", "Qty", "Buy Premium", "Sell Premium", "P&L", "Capital Left"])
                    w.writerow([datetime.now().strftime("%Y-%m-%d %H:%M:%S"), pos["symbol"], pos["qty"], round(pos["buy_price"], 2), round(pos["curr_ltp"], 2), round(pnl, 2), round(state["capital"], 2)])
            except Exception as ex: log_glitch("Journal Error", str(ex))

            state["positions"] = [p for p in state["positions"] if p["id"] != pos_id]

        capital_text.value = f"Capital: ₹{state['capital']:.2f}"
        stats_text.value = f"Trades: {state['trade_count']} | Peak Cap: ₹{state['peak_capital']:.0f} | Max DD: {state['max_drawdown_pct']:.2f}%"
        try: capital_text.update(); stats_text.update()
        except: pass
        refresh_positions_ui()

    def make_buy_handler(strike, side):
        return lambda e: place_order(strike, side)

    def make_exit_handler(pos_id):
        return lambda e: square_off_position(pos_id)

    def exit_all_positions(e):
        for pid in [p["id"] for p in list(state["positions"])]:
            square_off_position(pid)

    paper_trade_container = ft.Container(
        bgcolor="#0A1128", padding=12, border_radius=10, border=ft.border.all(1, ft.colors.BLUE_700),
        content=ft.Column([
            ft.Row([ft.Text("OPTION CHAIN (NIFTY, ATM ± 3)", weight=ft.FontWeight.BOLD, color=ft.colors.CYAN_400, size=12), ledger_btn], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
            option_chain_header,
            ft.Container(content=option_chain_list, bgcolor="#020409", padding=6, border_radius=6),
            ft.Divider(color=ft.colors.WHITE24, height=6),
            ft.Row([ft.Text("Lots (x50):", size=11), ft.IconButton(ft.icons.REMOVE_CIRCLE, on_click=lambda e: update_lots(-1), icon_color=ft.colors.RED_400), lot_val_txt, ft.IconButton(ft.icons.ADD_CIRCLE, on_click=lambda e: update_lots(1), icon_color=ft.colors.GREEN_400), ft.VerticalDivider(width=10, color=ft.colors.WHITE24), ft.Text("Auto-Exit (next Buy):", size=10), target_input, sl_input], alignment=ft.MainAxisAlignment.CENTER, wrap=True),
            order_message_txt,
            ft.Divider(color=ft.colors.WHITE24, height=6),
            ft.Row([ft.Text("LIVE PORTFOLIO", weight=ft.FontWeight.BOLD, color=ft.colors.CYAN_400, size=12), ft.Row([positions_count_txt, capital_text], spacing=10)], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
            positions_list,
            ft.Row([total_pnl_text, ft.ElevatedButton("EXIT ALL", bgcolor=ft.colors.RED_900, color="white", height=30, on_click=exit_all_positions)], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
            avail_fund_txt, stats_text
        ], spacing=6)
    )

    # ================= BACKTEST =================
    backtest_result_text = ft.Text("Initializing AI Backtest Engine...", size=11, color=ft.colors.WHITE)
    backtest_dialog = ft.AlertDialog(title=ft.Text("RANDOMIZED ALGO TUNER", size=14, weight=ft.FontWeight.BOLD, color=ft.colors.PURPLE_400), content=ft.Container(content=backtest_result_text, width=320, height=180, padding=8), bgcolor="#111B2D")
    page.overlay.append(backtest_dialog)

    def run_backtest(e):
        backtest_dialog.open = True
        backtest_result_text.value = "Fetching 2-Year Historical Dataset...\nRunning random window simulation..."
        backtest_result_text.color = ft.colors.WHITE
        page.update()
        def worker():
            try:
                df = fetch_history("^NSEI", "2y", "1d")
                if df is not None and not df.empty: df = df.dropna(subset=["Open", "High", "Low", "Close"])
                if df is None or df.empty or len(df) < 30: raise Exception("Insufficient data.")
                window_size = random.randint(20, min(150, len(df) - 10))
                start_idx = random.randint(0, max(0, len(df) - window_size - 1))
                test_df = df.iloc[start_idx:start_idx + window_size].copy()
                start_date, end_date = test_df.index[0].strftime("%d %b %Y"), test_df.index[-1].strftime("%d %b %Y")
                test_df["Typical"] = (test_df["High"] + test_df["Low"] + test_df["Close"]) / 3.0
                test_df["VWAP"] = test_df["Typical"].rolling(window=14, min_periods=1).mean()
                wins, total = 0, 0
                for i in range(14, len(test_df) - 1):
                    total += 1
                    c_close, c_vwap, n_close = test_df["Close"].iloc[i], test_df["VWAP"].iloc[i], test_df["Close"].iloc[i + 1]
                    if c_close > c_vwap and n_close > c_close: wins += 1
                    elif c_close < c_vwap and n_close < c_close: wins += 1
                losses = total - wins
                win_rate = (wins / total) * 100 if total else 0
                msg = quant_config.auto_tune(wins, losses, total)

                if win_rate >= 70: acc_color = ft.colors.GREEN_400
                elif win_rate >= 50: acc_color = ft.colors.YELLOW_400
                else: acc_color = ft.colors.RED_400

                backtest_result_text.value = f"Random Window: {start_date} to {end_date}\nScalps Simulated: {total}\nWins: {wins} | Losses: {losses}\nAccuracy: {win_rate:.1f}%\n\n{msg}"
                backtest_result_text.color = acc_color
            except Exception as ex:
                log_glitch("Backtest", str(ex))
                backtest_result_text.value = f"Backtest Error: {ex}"
                backtest_result_text.color = ft.colors.RED_400
            try: page.update()
            except: pass
        threading.Thread(target=worker, daemon=True).start()

    # ================= CORE SCAN & UPDATES =================
    def update_chart_fast(n_hist):
        try:
            recent = n_hist.tail(40)
            points, labels = [], []
            last_point_label = None
            for i, (idx, row) in enumerate(recent.iterrows()):
                c_val = float(safe_float(row["Close"]))
                x_val = float(i)
                time_str = idx.strftime("%H:%M")
                # v18.8 NOTE: confirmed via Flet's own source history that this Flet version
                # (0.24.x) runs jsonDecode() on the tooltip text client-side before showing it
                # (flet-dev PR #4069, "Linechart: jsonDecode tooltip before displaying"). A
                # plain string therefore shows up as raw escaped text -- it must be sent
                # already JSON-encoded so the client's decode step unwraps it correctly.
                tip_text = f"{idx.strftime('%d %b, %H:%M')} \u2022 \u20b9{c_val:,.2f}"
                last_point_label = tip_text
                try:
                    points.append(ft.LineChartDataPoint(x_val, c_val, tooltip=json.dumps(tip_text)))
                except Exception:
                    points.append(ft.LineChartDataPoint(x_val, c_val))
                if i % 8 == 0:
                    labels.append(ft.ChartAxisLabel(value=x_val, label=ft.Container(content=ft.Text(time_str, size=9, color=ft.colors.WHITE54), padding=ft.padding.only(top=5))))
            chart_series.data_points = points
            line_chart.bottom_axis = ft.ChartAxis(labels=labels, labels_size=32)
            if points: ys = [p.y for p in points]; line_chart.min_y, line_chart.max_y = min(ys) - 3, max(ys) + 3
            if last_point_label:
                try:
                    chart_last_point_text.value = f"Latest point: {last_point_label}"
                    chart_last_point_text.update()
                except Exception:
                    pass
        except Exception as ex: log_glitch("Chart", str(ex))

    def fetch_all_data():
        if not state["scan_lock"].acquire(blocking=False): return
        state["scanning"] = True; live_status.value = "Scanning NIFTY..."
        try: live_status.update()
        except: pass

        def task():
            try:
                n_hist = fetch_history("^NSEI", "5d", "1m")
                if n_hist is None or n_hist.empty: raise RuntimeError("NIFTY data unavailable")
                if "Volume" not in n_hist.columns or n_hist["Volume"].fillna(0).sum() == 0:
                    proxy = fetch_history("NIFTYBEES.NS", "5d", "1m")
                    if proxy is not None and not proxy.empty and "Volume" in proxy.columns: n_hist["Volume"] = proxy["Volume"]
                    else: n_hist["Volume"] = 0.0

                price = safe_float(n_hist["Close"].iloc[-1])
                day_high, day_low = safe_float(n_hist["High"].max()), safe_float(n_hist["Low"].min())
                prev_df = fetch_history("^NSEI", "5d", "1d")
                prev_close, prev_high, prev_low = resolve_prev_session(prev_df, price)  # v18.8: correct reference close (pre-market/weekend safe)
                pivot, s1, r1 = calculate_pivots(day_high, day_low, prev_close)
                atr_val = estimate_atr_15m(n_hist, 14) * quant_config.atr_multiplier  # v18.8: 15-min ATR (1-min ATR was ~1-2 pts)
                state["atr"] = atr_val  # store numeric ATR for Manual Analysis to reuse
                vwap_val = calculate_vwap(n_hist)
                volume_msg, vol_change_val = calculate_volume_signal(n_hist)
                state["volume_change_pct"] = vol_change_val  # NEW: store numeric volume change for Manual Analysis

                state["price"], state["anchor"], state["vwap"] = price, prev_close, vwap_val
                check_price_alerts(price)
                try:
                    vix_df = fetch_history("^INDIAVIX", "2d", "1d")
                    if vix_df is not None and not vix_df.empty: state["vix"] = safe_float(vix_df["Close"].iloc[-1], 14.0)
                except Exception as ex: log_glitch("VIX", str(ex))

                update_chart_fast(n_hist)

                price_text.value, sup_text.value, res_text.value, atr_text.value, vwap_text.value, vix_text.value = f"₹{price:,.2f}", f"{s1:.0f}", f"{r1:.0f}", f"{atr_val:.1f}", f"{vwap_val:.1f}", f"{state['vix']:.2f}"

                if state["capital"] <= 0:
                    risk_per_trade_txt.value = "₹0 (Capital Exhausted)"
                    sl_points_txt.value = "--"
                    safe_lots_txt.value = "0 Lots"
                else:
                    risk_amt = state["capital"] * 0.02
                    sl_pts = max(atr_val * 1.5, 1)
                    max_qty = risk_amt / sl_pts
                    safe_lots = max(1, int(max_qty // 50))
                    risk_per_trade_txt.value = f"₹{risk_amt:.0f} (2%)"
                    sl_points_txt.value = f"{sl_pts:.1f} pts"
                    safe_lots_txt.value = f"{safe_lots} Lots (x50)"

                state["atm_strike"] = round(price / 50) * 50
                refresh_option_chain()

                to_close = []
                for pos in list(state["positions"]):
                    current_prem = get_simulated_option_ltp(price, pos["strike"], pos["side"], state["vix"])
                    pos["curr_ltp"] = current_prem
                    pos["pnl"] = (current_prem - pos["buy_price"]) * pos["qty"]
                    if (pos["target_val"] > 0 and current_prem >= pos["target_val"]) or (pos["sl_val"] > 0 and current_prem <= pos["sl_val"]):
                        to_close.append(pos["id"])
                for pid in to_close:
                    square_off_position(pid)
                refresh_positions_ui()

                trend = "BULLISH" if price >= vwap_val else "BEARISH"
                engine_tech_text.value = f"VIX: {state['vix']:.2f} | ATR: {atr_val:.1f}\nVWAP Trend: {trend} ({pct_change(price, vwap_val):+.2f}%)."
                engine_live_text.value = f"Price ₹{price:,.2f} | Pivot {pivot:.0f}\nSupport {s1:.0f} / Resistance {r1:.0f}"
                e4_bias, e4_state, e4_strike, e4_opt, e4_zone = calculate_engine_4(price, prev_close)
                engine_4_text.value = f"Bias: {e4_bias} | {e4_state}\nStrike: {e4_strike} {e4_opt} | Zone: {e4_zone}"
                volume_spike_status.value, big_money_status.value = volume_msg, f"VWAP institutional bias: {trend}"

                candle_bull = safe_float(n_hist["Close"].iloc[-1]) >= safe_float(n_hist["Open"].iloc[-1])
                try:
                    _d = n_hist.index.date
                    _m = _d == _d[-1]
                    session_high, session_low = safe_float(n_hist["High"][_m].max()), safe_float(n_hist["Low"][_m].min())
                except Exception:
                    session_high, session_low = day_high, day_low
                levels = collect_levels(prev_high, prev_low, prev_close, session_high, session_low)
                state["levels"] = levels
                plan_atr = max(atr_val, price * 0.0005)  # floor so a dead-quiet market can't give a 0-point stop

                if price > vwap_val and candle_bull and e4_bias == "BULLISH":
                    signal, signal_color = "BULLISH SETUP (CALL)", ft.colors.GREEN_400
                    plan = build_trade_plan("LONG", price, plan_atr, levels)
                elif price < vwap_val and not candle_bull and e4_bias == "BEARISH":
                    signal, signal_color = "BEARISH SETUP (PUT)", ft.colors.RED_400
                    plan = build_trade_plan("SHORT", price, plan_atr, levels)
                else:
                    signal, signal_color = "NO TRADE ZONE / CHOPPY", ft.colors.YELLOW_400
                    plan = None

                state["verdict"], final_verdict_text.value, final_verdict_text.color, final_box.border = signal, signal, signal_color, ft.border.all(2, signal_color)
                render_trade_plan(plan, price, prev_close, vwap_val, plan_atr, levels)
                reason_text.value = state["latest_reason"] = f"REASON: Trend {trend}, Engine 4 {e4_bias}, News {state['macro']}, {volume_msg}."
                live_status.value = f"Scan OK"
                state["last_scan_ts"] = time.time()

                last_updated_text.value = f"Last updated: {datetime.now().strftime('%H:%M:%S')}"

                try: page.update()
                except: pass

            except Exception as ex: log_glitch("Main Data Fetch", f"{type(ex).__name__}: {ex}"); live_status.value = "Fetch Error"
            finally: state["scanning"] = False; state["scan_lock"].release()
        threading.Thread(target=task, daemon=True).start()

    def update_ohlc():
        try:
            hist_15m = fetch_history("^NSEI", "5d", "15m")
            if hist_15m is None or hist_15m.empty: return
            controls = []
            for index, row in hist_15m.tail(35).iterrows():
                op, hi, lo, cl = safe_float(row["Open"]), safe_float(row["High"]), safe_float(row["Low"]), safe_float(row["Close"])
                c_color = ft.colors.GREEN_300 if cl >= op else ft.colors.RED_300
                controls.append(ft.Row([ft.Text(index.strftime("%H:%M"), size=9, color=ft.colors.WHITE70, width=35), ft.Text(f"{op:.0f}", size=9, color=ft.colors.WHITE, width=45), ft.Text(f"{hi:.0f}", size=9, color=ft.colors.WHITE, width=45), ft.Text(f"{lo:.0f}", size=9, color=ft.colors.WHITE, width=45), ft.Text(f"{cl:.0f}", size=9, color=c_color, width=45, weight=ft.FontWeight.BOLD)]))
            ohlc_list.controls = controls
            try: ohlc_list.update()
            except: pass
        except Exception as ex: log_glitch("15M OHLC", str(ex))

    def update_secondary_radar():
        for sym, ref in [("^NSEBANK", sector_bank), ("^CNXIT", sector_it), ("^CNXAUTO", sector_auto), ("^CNXMETAL", sector_metal)]:
            try:
                df = fetch_history(sym, "2d", "1d")
                if df is None or df.empty: continue
                cur = safe_float(df["Close"].iloc[-1])
                prv = safe_float(df["Close"].iloc[-2]) if len(df) >= 2 else cur
                pct = pct_change(cur, prv)
                ref.value, ref.color = f"{cur:,.1f} ({pct:+.1f}%)", ft.colors.GREEN_400 if pct >= 0 else ft.colors.RED_400
                ref.update()
            except Exception as ex: log_glitch(f"Sector {sym}", str(ex))

        for sym, ref in [("HDFCBANK.NS", hdfc_txt), ("RELIANCE.NS", rel_txt), ("^DJI", dow_txt), ("CL=F", crude_txt)]:
            try:
                df = fetch_history(sym, "2d", "1d")
                if df is None or df.empty: continue
                cur = safe_float(df["Close"].iloc[-1])
                prv = safe_float(df["Close"].iloc[-2]) if len(df) >= 2 else cur
                pct = pct_change(cur, prv)
                ref.value, ref.color = f"{cur:,.1f} ({pct:+.1f}%)", ft.colors.GREEN_400 if pct >= 0 else ft.colors.RED_400
                ref.update()
            except Exception as ex: log_glitch(f"Radar {sym}", str(ex))

    def secondary_data_worker():
        last_ohlc = last_radar = 0
        while state["running"]:
            now = time.time()
            if now - last_ohlc >= 60: last_ohlc = now; update_ohlc()
            if now - last_radar >= 60: last_radar = now; threading.Thread(target=update_secondary_radar, daemon=True).start()
            time.sleep(2)

    def realtime_news_worker():
        while state["running"]:
            try:
                sent, items = fetch_live_news()
                state["macro"], state["news_items"] = sent, items
                if items:
                    top = items[0]
                    live_news_ticker.value = f"LIVE MACRO: {top['title']} [{top['sentiment']}]"
                    engine_news_text.value = "\n".join([f"Overall: {sent}"] + [f"{x['sentiment']}: {x['title']}" for x in items[:3]])
                else:
                    live_news_ticker.value = "LIVE MACRO: No fresh headline received."
                    engine_news_text.value = "Live macro feed temporarily unavailable."
                try: live_news_ticker.update(); engine_news_text.update()
                except: pass
            except Exception as ex: log_glitch("Live News", str(ex))
            for _ in range(45):
                if not state["running"]: break
                time.sleep(1)

    auto_scan_switch = ft.Switch(label="Auto Scan", value=False, active_color=ft.colors.GREEN_400)
    auto_scan_interval_dd = ft.Dropdown(
        width=90, height=35, text_size=10, content_padding=5, value="5",
        options=[ft.dropdown.Option("5", "5s"), ft.dropdown.Option("15", "15s"), ft.dropdown.Option("30", "30s"), ft.dropdown.Option("60", "60s")]
    )
    controls_row = ft.Row([
        ft.ElevatedButton("LIVE SCAN", icon=ft.icons.RADAR, bgcolor=ft.colors.BLUE_700, color=ft.colors.WHITE, on_click=lambda e: fetch_all_data()),
        ft.ElevatedButton("ULTIMATE SCALP", icon=ft.icons.STAR, bgcolor=ft.colors.PURPLE_700, color=ft.colors.WHITE, on_click=run_backtest),
        auto_scan_switch, auto_scan_interval_dd
    ], alignment=ft.MainAxisAlignment.SPACE_EVENLY)

    def auto_scan_worker():
        while state["running"]:
            try:
                if auto_scan_switch.value and not state["scanning"]: fetch_all_data()
            except Exception as ex: log_glitch("Auto Scan", str(ex))
            try:
                interval = int(auto_scan_interval_dd.value)
            except Exception:
                interval = 5
            time.sleep(max(interval, 1))

    def clock_worker():
        while state["running"]:
            now = datetime.now()
            time_text.value = now.strftime("%d %b %Y | %H:%M:%S")
            if is_market_open(now):
                market_status_text.value = "🟢 Market OPEN"
                market_status_text.color = ft.colors.GREEN_400
            else:
                market_status_text.value = "🔴 Market CLOSED — showing last available data"
                market_status_text.color = ft.colors.RED_300
            try:
                time_text.update()
                market_status_text.update()
            except: pass
            time.sleep(1)

    # NEW: background auto-verification of manual predictions (checks every 5 min)
    def prediction_auto_verify_worker():
        while state["running"]:
            try:
                n = verify_predictions()
                if n:
                    refresh_prediction_history()
                    update_manual_accuracy_banner()
                    try: page.update()
                    except: pass
            except Exception as ex:
                log_glitch("Auto Verify", str(ex))
            for _ in range(300):
                if not state["running"]: break
                time.sleep(1)

    dev_dialog = ft.AlertDialog(title=ft.Text("WATCHDOG (Glitch & Lag History)", color=ft.colors.ORANGE_400, weight=ft.FontWeight.BOLD), content=ft.Container(dev_list, width=320, height=350, bgcolor=ft.colors.BLACK87, padding=10), actions=[ft.ElevatedButton("Clear Logs", on_click=lambda e: (state["glitch_logs"].clear(), open_dev_menu(e)))])
    page.overlay.append(dev_dialog)
    render_notes()

    threading.Thread(target=auto_scan_worker, daemon=True).start()
    threading.Thread(target=realtime_news_worker, daemon=True).start()
    threading.Thread(target=clock_worker, daemon=True).start()
    threading.Thread(target=secondary_data_worker, daemon=True).start()
    threading.Thread(target=prediction_auto_verify_worker, daemon=True).start()
    threading.Thread(target=alert_poll_worker, daemon=True).start()

    # ================= MOBILE NAVIGATION (v19.0) =================
    # Every widget below is the exact same object built earlier in this file --
    # nothing new is created except the navigation chrome itself (top bar +
    # hamburger menu + the container that swaps which screen is showing).
    # Only proven-safe control types are used here (Container/Row/Column/Text/
    # ElevatedButton, all already used successfully elsewhere in this file) --
    # no ft.Icon() with new icon names, no NavigationDrawer/Tabs, to avoid the
    # kind of Flet-version mismatch that broke the chart tooltip earlier.

    top_pnl_badge = ft.Text("", size=13, weight=ft.FontWeight.BOLD, color=ft.colors.WHITE)

    home_screen = ft.Column([
        ft.Row([ft.Column([ft.Text("NIFTY QUANT AI", size=18, weight=ft.FontWeight.W_900, color=ft.colors.BLUE_400), app_title], spacing=1), time_text], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
        ft.Row([market_status_text, last_updated_text], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
        alert_banner,
        chart_container, data_row,
        ft.Row([ft.Text("INSTITUTIONAL FLOW", weight=ft.FontWeight.BOLD, color=ft.colors.GREEN_400, size=11)]),
        ft.Container(bgcolor="#020409", padding=6, border_radius=6, content=ft.Column([
            ft.Row([ft.Text("BIG MONEY:", size=8, color=ft.colors.WHITE54), big_money_status]),
            ft.Row([ft.Text("VOLUME:", size=8, color=ft.colors.WHITE54), volume_spike_status]),
            ft.Row([ft.Text("OI DATA:", size=8, color=ft.colors.WHITE54), oi_change_status])
        ], spacing=2)),
        ft.Row([box_news, box_tech], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
        ft.Row([box_live, box_engine4], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
        final_box, news_ticker_box, controls_row
    ], horizontal_alignment=ft.CrossAxisAlignment.STRETCH, spacing=6, scroll=ft.ScrollMode.AUTO, expand=True)

    trade_screen = ft.Column([
        ft.Text("💹 PAPER TRADING", size=16, weight=ft.FontWeight.BOLD, color=ft.colors.CYAN_400),
        ft.Row([ft.Icon(ft.icons.SHIELD, color=ft.colors.RED_400, size=14), ft.Text("DYNAMIC RISK MANAGER", weight=ft.FontWeight.BOLD, color=ft.colors.RED_400, size=11)]),
        ft.Container(bgcolor="#020409", padding=8, border_radius=6, border=ft.border.all(1, ft.colors.RED_900), content=ft.Column([
            ft.Row([ft.Text("Risk per Trade:", size=10, color=ft.colors.WHITE70), risk_per_trade_txt], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
            ft.Row([ft.Text("Suggested SL:", size=10, color=ft.colors.WHITE70), sl_points_txt], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
            ft.Row([ft.Text("Max Safe Lots:", size=10, color=ft.colors.WHITE70), safe_lots_txt], alignment=ft.MainAxisAlignment.SPACE_BETWEEN)
        ], spacing=4)),
        paper_trade_container
    ], spacing=8, scroll=ft.ScrollMode.AUTO, expand=True)

    manual_screen = ft.Column([
        ft.Text("🧮 MANUAL MARKET ANALYSIS", size=16, weight=ft.FontWeight.BOLD, color=ft.colors.TEAL_300),
        manual_analysis_box
    ], spacing=8, scroll=ft.ScrollMode.AUTO, expand=True)

    alerts_screen = ft.Column([
        ft.Text("🔔 ALERTS & NOTEPAD", size=16, weight=ft.FontWeight.BOLD, color=ft.colors.YELLOW_400),
        alerts_section
    ], spacing=8, scroll=ft.ScrollMode.AUTO, expand=True)

    radar_screen = ft.Column([
        ft.Text("🌐 SECTORS & GLOBAL RADAR", size=16, weight=ft.FontWeight.BOLD, color=ft.colors.ORANGE_400),
        ft.Container(bgcolor="#020409", padding=8, border_radius=6, border=ft.border.all(1, ft.colors.ORANGE_900), content=ft.Column([
            ticker_row("BANK NIFTY", sector_bank), ft.Divider(color=ft.colors.WHITE10, height=1),
            ticker_row("NIFTY IT", sector_it), ft.Divider(color=ft.colors.WHITE10, height=1),
            ticker_row("NIFTY AUTO", sector_auto), ft.Divider(color=ft.colors.WHITE10, height=1),
            ticker_row("NIFTY METAL", sector_metal)
        ], spacing=4)),
        ft.Text("NIFTY HEAVYWEIGHTS", size=9, color=ft.colors.WHITE54), ticker_row("HDFC BANK", hdfc_txt), ticker_row("RELIANCE", rel_txt),
        ft.Text("GLOBAL SENTIMENT", size=9, color=ft.colors.WHITE54), ticker_row("DOW JONES (US)", dow_txt), ticker_row("CRUDE OIL", crude_txt),
        ft.Row([ft.Icon(ft.icons.ACCESS_TIME, color=ft.colors.CYAN_400, size=14), ft.Text("15-MIN OHLC DATA", weight=ft.FontWeight.BOLD, color=ft.colors.CYAN_400, size=11)]),
        ft.Row([ft.Text("TIME", size=8, color=ft.colors.WHITE54, width=35), ft.Text("OPEN", size=8, color=ft.colors.WHITE54, width=45), ft.Text("HIGH", size=8, color=ft.colors.WHITE54, width=45), ft.Text("LOW", size=8, color=ft.colors.WHITE54, width=45), ft.Text("CLOSE", size=8, color=ft.colors.WHITE54, width=45)]),
        ft.Container(content=ohlc_list, height=300, bgcolor="#020409", padding=5, border_radius=6)
    ], spacing=8, scroll=ft.ScrollMode.AUTO, expand=True)

    chat_screen = ft.Column([
        ft.Row([ft.Icon(ft.icons.SUPPORT_AGENT, color=ft.colors.BLUE_400, size=16), ft.Text("SMART LOCAL MENTOR", weight=ft.FontWeight.BOLD, color=ft.colors.BLUE_400, size=16)]),
        ft.Container(content=chat_list, expand=True, bgcolor="#020409", padding=6, border_radius=6),
        ft.Row([user_input, ft.IconButton(icon=ft.icons.SEND, icon_size=16, icon_color=ft.colors.BLUE_400, on_click=send_ai_message)], spacing=2)
    ], spacing=8, expand=True)

    screens = {"home": home_screen, "trade": trade_screen, "manual": manual_screen,
               "alerts": alerts_screen, "radar": radar_screen, "chat": chat_screen}

    body_container = ft.Container(content=home_screen, expand=True, padding=10)

    def close_nav_menu():
        nav_menu_dialog.open = False
        try: page.update()
        except: pass

    def go_to_screen(name):
        def handler(e):
            body_container.content = screens[name]
            close_nav_menu()
            try: body_container.update()
            except Exception as ex: log_glitch("Navigation", str(ex))
        return handler

    def menu_row(emoji_label, screen_name):
        return ft.Container(
            padding=14, border_radius=8, bgcolor="#0A1128", on_click=go_to_screen(screen_name),
            content=ft.Text(emoji_label, size=14, color=ft.colors.WHITE, weight=ft.FontWeight.BOLD)
        )

    nav_menu_dialog = ft.AlertDialog(
        title=ft.Text("☰ MENU", color=ft.colors.CYAN_300, weight=ft.FontWeight.BOLD),
        content=ft.Container(width=260, content=ft.Column([
            menu_row("📊  Home", "home"),
            menu_row("💹  Paper Trading", "trade"),
            menu_row("🧮  Manual Analysis", "manual"),
            menu_row("🔔  Alerts & Notepad", "alerts"),
            menu_row("🌐  Sectors & Radar", "radar"),
            menu_row("🤖  Chat Mentor", "chat"),
        ], spacing=6, tight=True)),
        actions=[ft.ElevatedButton("Close", on_click=lambda e: close_nav_menu())]
    )
    page.overlay.append(nav_menu_dialog)

    def open_nav_menu(e):
        nav_menu_dialog.open = True
        try: page.update()
        except: pass

    menu_button = ft.ElevatedButton("☰", bgcolor=ft.colors.BLUE_GREY_900, color="white", height=40, width=50, on_click=open_nav_menu)

    top_bar = ft.Container(
        bgcolor="#0A1128", padding=10, border=ft.border.only(bottom=ft.border.BorderSide(1, "#1C2A4A")),
        content=ft.Row([
            menu_button,
            ft.Column([price_text, live_status], spacing=0, expand=True),
            ft.Column([top_pnl_badge], horizontal_alignment=ft.CrossAxisAlignment.END)
        ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN, vertical_alignment=ft.CrossAxisAlignment.CENTER)
    )

    page.add(ft.Column([top_bar, body_container], expand=True, spacing=0))
    page.on_close = lambda _: state.update({"running": False})

    # FIX v18.6: these must run AFTER page.add() -- calling .update() on a
    # control before it's attached to the page threw a harmless but noisy
    # "Control must be added to the page first" entry in the Watchdog log.
    # The displayed values were always correct on first paint either way;
    # this only removes the false-alarm log entries.
    refresh_prediction_history()
    update_manual_accuracy_banner()
    refresh_positions_ui()
    render_alerts()

if __name__ == "__main__":
    ft.app(target=main)
