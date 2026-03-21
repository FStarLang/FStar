#!/usr/bin/env python3
"""
ramon-report.py — Generate a visual performance comparison report from
two directories of .ramon files (produced by the `ramon` tool).

Usage:
    python3 ramon-report.py <baseline_dir> <patched_dir> [--output report.html]
    python3 ramon-report.py <baseline_dir> <patched_dir> -o report.md

Produces an HTML or Markdown report with:
  - Summary statistics (median/mean/geo mean/std dev/percentiles)
  - Change distribution (improved/unchanged/regressed counts)
  - Memory and time scatter plots (HTML only)
  - Top regressions and improvements tables
  - Full comparison table

The output format can be chosen with --format, or auto-detected from
the output filename extension (.md → markdown, .html → HTML).
"""

import os
import sys
import argparse
import json
import math
import re
from collections import defaultdict
from statistics import median, mean, stdev

# ── Parsing ──────────────────────────────────────────────────────────────────

def parse_time(s):
    m = re.search(r'([\d.]+)s', s)
    return float(m.group(1)) if m else 0.0

def parse_mem(s):
    m = re.search(r'(\d+)\s*(KiB|MiB|GiB|B)', s)
    if not m:
        return 0
    val = int(m.group(1))
    unit = m.group(2)
    if unit == "KiB":  val *= 1024
    elif unit == "MiB": val *= 1024 * 1024
    elif unit == "GiB": val *= 1024 * 1024 * 1024
    return val

def humanize(n):
    for suf in ['B', 'KiB', 'MiB', 'GiB', 'TiB']:
        if abs(n) < 1024:
            return f"{n:.1f} {suf}"
        n /= 1024
    return f"{n:.1f} TiB"

def load_ramon_file(fn):
    ret = {"fn": fn}
    try:
        with open(fn) as f:
            for line in f:
                parts = line.split(None, 1)
                if len(parts) < 2: continue
                key, val = parts[0], parts[1].strip()
                if key == "group.total":     ret["time"] = parse_time(val)
                elif key == "group.utime":   ret["utime"] = parse_time(val)
                elif key == "group.stime":   ret["stime"] = parse_time(val)
                elif key == "group.mempeak": ret["mem"] = parse_mem(val)
                elif key == "exitcode":      ret["rc"] = int(val)
                elif key == "walltime":      ret["wall"] = parse_time(val)
    except Exception as e:
        return None
    if "rc" not in ret or "time" not in ret or "mem" not in ret:
        return None

    # Prefer F*-only memory (excludes Z3) from companion .fstarmem file.
    fstarmem_fn = fn.removesuffix(".ramon") + ".fstarmem"
    try:
        with open(fstarmem_fn) as f:
            for line in f:
                parts = line.split(None, 1)
                if len(parts) >= 2 and parts[0] == "fstar.mempeak":
                    ret["mem"] = int(parts[1].strip())
                    break
    except FileNotFoundError:
        pass

    return ret

def find_ramon_files(root):
    result = []
    for dirpath, _, filenames in os.walk(root):
        for f in filenames:
            if f.endswith(".ramon"):
                result.append(os.path.join(dirpath, f))
    return sorted(result)

def make_matching(root1, root2, files1, files2):
    d1 = {}
    d2 = {}
    for f in files1:
        r = load_ramon_file(f)
        if r and r.get("rc", 1) == 0:
            key = os.path.relpath(f, root1).removesuffix(".ramon")
            d1[key] = r
    for f in files2:
        r = load_ramon_file(f)
        if r and r.get("rc", 1) == 0:
            key = os.path.relpath(f, root2).removesuffix(".ramon")
            d2[key] = r
    matches = []
    for key in sorted(set(d1.keys()) & set(d2.keys())):
        matches.append({
            "fn": key,
            "l": d1[key],
            "r": d2[key],
        })
    return matches, d1, d2

# ── Helpers ──────────────────────────────────────────────────────────────────

def percentile(sorted_data, p):
    """Compute the p-th percentile of already-sorted data."""
    if not sorted_data:
        return 0
    k = (len(sorted_data) - 1) * p / 100
    f = int(k)
    c = min(f + 1, len(sorted_data) - 1)
    return sorted_data[f] + (k - f) * (sorted_data[c] - sorted_data[f])

def geo_mean(ratios):
    """Geometric mean of a list of positive ratios."""
    valid = [r for r in ratios if r > 0]
    if not valid:
        return 1.0
    log_sum = sum(math.log(r) for r in valid)
    return math.exp(log_sum / len(valid))

# ── Statistics ───────────────────────────────────────────────────────────────

CHANGE_THRESHOLD = 5  # percent: changes beyond ±this are "significant"

def compute_stats(matches):
    if not matches: return {}

    mem_pcts = [(m["r"]["mem"] - m["l"]["mem"]) / m["l"]["mem"] * 100
                for m in matches if m["l"]["mem"] > 0]
    time_pcts = [(m["r"]["time"] - m["l"]["time"]) / m["l"]["time"] * 100
                 for m in matches if m["l"]["time"] > 0.1]  # skip very fast tests
    mem_diffs = [m["r"]["mem"] - m["l"]["mem"] for m in matches]
    time_diffs = [m["r"]["time"] - m["l"]["time"] for m in matches]

    # Ratios for geometric mean (patched / baseline)
    mem_ratios = [m["r"]["mem"] / m["l"]["mem"]
                  for m in matches if m["l"]["mem"] > 0]
    time_ratios = [m["r"]["time"] / m["l"]["time"]
                   for m in matches if m["l"]["time"] > 0.1]

    # Heavy tests: baseline mem > 100 MiB
    heavy = [m for m in matches if m["l"]["mem"] > 100 * 1024 * 1024]
    heavy_mem_pcts = [(m["r"]["mem"] - m["l"]["mem"]) / m["l"]["mem"] * 100
                      for m in heavy if m["l"]["mem"] > 0]
    heavy_time_pcts = [(m["r"]["time"] - m["l"]["time"]) / m["l"]["time"] * 100
                       for m in heavy if m["l"]["time"] > 0.1]
    heavy_mem_ratios = [m["r"]["mem"] / m["l"]["mem"]
                        for m in heavy if m["l"]["mem"] > 0]
    heavy_time_ratios = [m["r"]["time"] / m["l"]["time"]
                         for m in heavy if m["l"]["time"] > 0.1]

    def mk_stats(xs, ratios=None):
        if not xs:
            return {"median": 0, "mean": 0, "stdev": 0,
                    "min": 0, "max": 0,
                    "p5": 0, "p25": 0, "p75": 0, "p95": 0,
                    "count": 0, "geo_mean": 1.0,
                    "n_improved": 0, "n_regressed": 0, "n_unchanged": 0}
        s = sorted(xs)
        return {
            "median": median(xs),
            "mean": mean(xs),
            "stdev": stdev(xs) if len(xs) > 1 else 0.0,
            "min": min(xs),
            "max": max(xs),
            "p5": percentile(s, 5),
            "p25": percentile(s, 25),
            "p75": percentile(s, 75),
            "p95": percentile(s, 95),
            "count": len(xs),
            "geo_mean": geo_mean(ratios) if ratios else 1.0,
            "n_improved": sum(1 for x in xs if x < -CHANGE_THRESHOLD),
            "n_regressed": sum(1 for x in xs if x > CHANGE_THRESHOLD),
            "n_unchanged": sum(1 for x in xs if -CHANGE_THRESHOLD <= x <= CHANGE_THRESHOLD),
        }

    return {
        "mem_pct": mk_stats(mem_pcts, mem_ratios),
        "time_pct": mk_stats(time_pcts, time_ratios),
        "mem_abs": mk_stats(mem_diffs),
        "time_abs": mk_stats(time_diffs),
        "heavy_mem_pct": mk_stats(heavy_mem_pcts, heavy_mem_ratios),
        "heavy_time_pct": mk_stats(heavy_time_pcts, heavy_time_ratios),
        "n_matches": len(matches),
        "n_heavy": len(heavy),
        "total_mem_diff": sum(m["r"]["mem"] - m["l"]["mem"] for m in matches),
        "total_time_diff": sum(m["r"]["time"] - m["l"]["time"] for m in matches),
    }

# ── Markdown Report ──────────────────────────────────────────────────────────

def generate_markdown(matches, stats, lhs_label, rhs_label):
    s = stats
    mp = s["mem_pct"]
    tp = s["time_pct"]
    hm = s["heavy_mem_pct"]
    ht = s["heavy_time_pct"]

    def sgn(x):
        return f"+{x:.1f}" if x >= 0 else f"{x:.1f}"

    def pct_md(base, new):
        if base == 0: return "N/A"
        p = (new - base) / base * 100
        return f"{sgn(p)}%"

    by_mem_diff = sorted(matches, key=lambda m: m["r"]["mem"] - m["l"]["mem"])
    by_time_diff = sorted(matches, key=lambda m: m["r"]["time"] - m["l"]["time"])

    def md_table(items, n=20):
        rows = []
        rows.append("| File | Mem (base) | Mem (patch) | Mem Δ | Time (base) | Time (patch) | Time Δ |")
        rows.append("|------|----------:|----------:|------:|----------:|----------:|------:|")
        for m in items[:n]:
            fn = m["fn"]
            if len(fn) > 60:
                fn = "…" + fn[-59:]
            lm, rm = m["l"]["mem"], m["r"]["mem"]
            lt, rt = m["l"]["time"], m["r"]["time"]
            rows.append(f"| `{fn}` | {humanize(lm)} | {humanize(rm)} | {pct_md(lm, rm)} | {lt:.2f}s | {rt:.2f}s | {pct_md(lt, rt)} |")
        return "\n".join(rows)

    L = []

    L.append("## 🔬 F* Performance Comparison\n")
    L.append(f"**Baseline:** `{lhs_label}` | **Patched:** `{rhs_label}` | **Matched:** {s['n_matches']} tests\n")

    # ── Summary table ──
    L.append("### Summary\n")
    L.append(
        "| Metric "
        "| <abbr title=\"Middle value: half of tests changed less, half changed more\">Median</abbr> "
        "| <abbr title=\"Arithmetic mean of all percentage changes\">Mean</abbr> "
        "| <abbr title=\"Geometric mean of patched/baseline ratios. Best summary for performance: 1.0× = no change, &lt;1× = improvement. Symmetric: 2× speedup and 2× slowdown cancel out\">Geo Mean</abbr> "
        "| <abbr title=\"Standard deviation: measures how spread out the changes are. Low = consistent, high = variable\">Std Dev</abbr> "
        "| <abbr title=\"5th to 95th percentile range: the middle 90% of changes fall in this interval, ignoring outliers\">P5 → P95</abbr> "
        "| <abbr title=\"Absolute minimum and maximum change observed\">Min → Max</abbr> |"
    )
    L.append("|--------|-------:|-----:|---------:|--------:|---------:|----------:|")
    L.append(f"| **Memory** | {sgn(mp['median'])}% | {sgn(mp['mean'])}% | {mp['geo_mean']:.3f}× | {mp['stdev']:.1f}% | {sgn(mp['p5'])}% → {sgn(mp['p95'])}% | {sgn(mp['min'])}% → {sgn(mp['max'])}% |")
    L.append(f"| **Time** | {sgn(tp['median'])}% | {sgn(tp['mean'])}% | {tp['geo_mean']:.3f}× | {tp['stdev']:.1f}% | {sgn(tp['p5'])}% → {sgn(tp['p95'])}% | {sgn(tp['min'])}% → {sgn(tp['max'])}% |")
    L.append("")
    L.append(f"**Totals:** Memory: {humanize(s['total_mem_diff'])} | Time: {sgn(s['total_time_diff'])}s\n")

    # ── Distribution ──
    L.append("### Change Distribution\n")
    L.append(
        "| Metric "
        "| <abbr title=\"Tests where the metric decreased by more than 5%\">🟢 Improved (&gt;5%)</abbr> "
        "| <abbr title=\"Tests where the metric changed by less than ±5%\">⚪ Unchanged (±5%)</abbr> "
        "| <abbr title=\"Tests where the metric increased by more than 5%\">🔴 Regressed (&gt;5%)</abbr> |"
    )
    L.append("|--------|-------------------:|--------------------:|--------------------:|")
    for label, st in [("Memory", mp), ("Time", tp)]:
        total = st['n_improved'] + st['n_unchanged'] + st['n_regressed']
        if total > 0:
            L.append(f"| **{label}** | {st['n_improved']} ({st['n_improved']/total*100:.0f}%) | {st['n_unchanged']} ({st['n_unchanged']/total*100:.0f}%) | {st['n_regressed']} ({st['n_regressed']/total*100:.0f}%) |")
    L.append("")

    # ── Heavy tests ──
    if s['n_heavy'] > 0:
        L.append(f"### Heavy Tests (baseline > 100 MiB, n={s['n_heavy']})\n")
        L.append(
            "| Metric "
            "| <abbr title=\"Middle value: half of tests changed less, half changed more\">Median</abbr> "
            "| <abbr title=\"Arithmetic mean of all percentage changes\">Mean</abbr> "
            "| <abbr title=\"Geometric mean of patched/baseline ratios (1.0× = no change, &lt;1× = improvement)\">Geo Mean</abbr> "
            "| <abbr title=\"Standard deviation: measures how spread out the changes are\">Std Dev</abbr> "
            "| <abbr title=\"5th to 95th percentile range: the middle 90% of changes, ignoring outliers\">P5 → P95</abbr> |"
        )
        L.append("|--------|-------:|-----:|---------:|--------:|---------:|")
        L.append(f"| **Memory** | {sgn(hm['median'])}% | {sgn(hm['mean'])}% | {hm['geo_mean']:.3f}× | {hm['stdev']:.1f}% | {sgn(hm['p5'])}% → {sgn(hm['p95'])}% |")
        L.append(f"| **Time** | {sgn(ht['median'])}% | {sgn(ht['mean'])}% | {ht['geo_mean']:.3f}× | {ht['stdev']:.1f}% | {sgn(ht['p5'])}% → {sgn(ht['p95'])}% |")
        L.append("")

    # ── Top tables ──
    L.append("<details><summary>📉 Top 20 Memory Improvements</summary>\n")
    L.append(md_table(by_mem_diff[:20]))
    L.append("\n</details>\n")

    L.append("<details><summary>📈 Top 20 Memory Regressions</summary>\n")
    L.append(md_table(list(reversed(by_mem_diff[-20:]))))
    L.append("\n</details>\n")

    L.append("<details><summary>⬇️ Top 20 Time Improvements</summary>\n")
    L.append(md_table(by_time_diff[:20]))
    L.append("\n</details>\n")

    L.append("<details><summary>⬆️ Top 20 Time Regressions</summary>\n")
    L.append(md_table(list(reversed(by_time_diff[-20:]))))
    L.append("\n</details>\n")

    # ── Full comparison ──
    L.append(f"<details><summary>📋 Full Comparison ({s['n_matches']} tests)</summary>\n")
    L.append(md_table(sorted(matches, key=lambda m: m["fn"]), n=len(matches)))
    L.append("\n</details>\n")

    # ── Notes ──
    L.append("---\n")
    L.append("> **Note:** Memory values report the peak OCaml heap of the F\\* process (excluding Z3 subprocesses). "
             "Time measurements are from single runs and may be noisy, especially for fast tests. "
             "Tests with baseline time < 0.1s are excluded from time statistics. "
             "The geometric mean (Geo Mean) of the patched/baseline ratio is the most robust summary "
             "statistic for performance comparisons (1.0× = no change, <1× = improvement).")

    return "\n".join(L)

# ── HTML Report ──────────────────────────────────────────────────────────────

def generate_html(matches, stats, lhs_label, rhs_label):
    # Prepare data for charts
    mem_data = []
    time_data = []
    for m in matches:
        short = m["fn"].split("/")[-1] if "/" in m["fn"] else m["fn"]
        mem_data.append({
            "name": short,
            "full": m["fn"],
            "base": m["l"]["mem"] / (1024*1024),
            "patch": m["r"]["mem"] / (1024*1024),
        })
        time_data.append({
            "name": short,
            "full": m["fn"],
            "base": m["l"]["time"],
            "patch": m["r"]["time"],
        })

    # Sort matches for tables
    by_mem_diff = sorted(matches, key=lambda m: m["r"]["mem"] - m["l"]["mem"])
    by_time_diff = sorted(matches, key=lambda m: m["r"]["time"] - m["l"]["time"])
    by_mem_pct = sorted(matches, key=lambda m: (m["r"]["mem"] - m["l"]["mem"]) / max(m["l"]["mem"], 1))

    s = stats
    mp = s["mem_pct"]
    tp = s["time_pct"]
    hm = s["heavy_mem_pct"]
    ht = s["heavy_time_pct"]

    # Build histogram data for memory % changes
    mem_pct_list = [(m["r"]["mem"] - m["l"]["mem"]) / max(m["l"]["mem"], 1) * 100
                    for m in matches]
    hist_bins = list(range(-35, 15, 1))
    hist_counts = [0] * (len(hist_bins) - 1)
    for p in mem_pct_list:
        for i in range(len(hist_bins) - 1):
            if hist_bins[i] <= p < hist_bins[i+1]:
                hist_counts[i] += 1
                break

    def pct(base, new):
        if base == 0: return "N/A"
        p = (new - base) / base * 100
        color = "green" if p < -1 else ("red" if p > 1 else "gray")
        sign = "+" if p > 0 else ""
        return f'<span style="color:{color};font-weight:bold">{sign}{p:.1f}%</span>'

    def row(m):
        fn = m["fn"]
        lm, rm = m["l"]["mem"], m["r"]["mem"]
        lt, rt = m["l"]["time"], m["r"]["time"]
        return f"""<tr>
            <td style="font-family:monospace;font-size:0.8em" title="{fn}">{fn[-80:]}</td>
            <td style="text-align:right">{humanize(lm)}</td>
            <td style="text-align:right">{humanize(rm)}</td>
            <td style="text-align:right">{pct(lm, rm)}</td>
            <td style="text-align:right">{lt:.2f}s</td>
            <td style="text-align:right">{rt:.2f}s</td>
            <td style="text-align:right">{pct(lt, rt)}</td>
        </tr>"""

    def table(items, n=20):
        hdr = """<table style="border-collapse:collapse;width:100%;font-size:0.85em">
        <tr style="background:#f0f0f0"><th>File</th>
            <th>Mem (base)</th><th>Mem (patch)</th><th>Mem Δ</th>
            <th>Time (base)</th><th>Time (patch)</th><th>Time Δ</th></tr>"""
        rows = "\n".join(row(m) for m in items[:n])
        return hdr + rows + "</table>"

    def stat_class(val, invert=False):
        if invert:
            return 'good' if val > 1 else ('bad' if val < -1 else 'neutral')
        return 'good' if val < -1 else ('bad' if val > 1 else 'neutral')

    html = f"""<!DOCTYPE html>
<html><head>
<meta charset="utf-8">
<title>F* Performance Comparison Report</title>
<style>
body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; margin: 2em; background: #fafafa; }}
h1 {{ color: #333; border-bottom: 2px solid #0366d6; padding-bottom: 0.3em; }}
h2 {{ color: #444; margin-top: 2em; }}
.summary {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 1em; margin: 1em 0; }}
.card {{ background: white; border-radius: 8px; padding: 1.2em; box-shadow: 0 1px 3px rgba(0,0,0,0.1); }}
.card h3 {{ margin: 0 0 0.5em; color: #555; font-size: 0.9em; text-transform: uppercase; }}
.card .value {{ font-size: 1.8em; font-weight: bold; }}
.card .detail {{ color: #888; font-size: 0.85em; margin-top: 0.3em; }}
.good {{ color: #22863a; }}
.bad {{ color: #cb2431; }}
.neutral {{ color: #6a737d; }}
table {{ border-collapse: collapse; width: 100%; }}
th, td {{ padding: 4px 8px; border-bottom: 1px solid #eee; }}
tr:hover {{ background: #f8f8ff; }}
canvas {{ max-width: 100%; margin: 1em 0; }}
details {{ margin: 0.5em 0; }}
summary {{ cursor: pointer; font-weight: bold; padding: 0.5em; background: #f0f0f0; border-radius: 4px; }}
.dist-bar {{ display: inline-block; height: 1em; vertical-align: middle; }}
.note {{ background: #fff8e1; border-left: 4px solid #ffc107; padding: 0.8em 1em; margin: 1em 0; font-size: 0.9em; color: #666; }}
</style>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4"></script>
</head><body>
<h1>🔬 F* Performance Comparison Report</h1>
<p><strong>Baseline:</strong> {lhs_label}<br>
<strong>Patched:</strong> {rhs_label}<br>
<strong>Matched tests:</strong> {s["n_matches"]}</p>

<div class="summary">
    <div class="card">
        <h3>Memory Change (median)</h3>
        <div class="value {stat_class(mp['median'])}">{mp['median']:+.1f}%</div>
        <div class="detail">mean: {mp['mean']:+.1f}% · geo mean: {mp['geo_mean']:.3f}× · σ: {mp['stdev']:.1f}%</div>
        <div class="detail">P5–P95: [{mp['p5']:+.1f}%, {mp['p95']:+.1f}%] · range: [{mp['min']:+.1f}%, {mp['max']:+.1f}%]</div>
    </div>
    <div class="card">
        <h3>Time Change (median)</h3>
        <div class="value {stat_class(tp['median'])}">{tp['median']:+.1f}%</div>
        <div class="detail">mean: {tp['mean']:+.1f}% · geo mean: {tp['geo_mean']:.3f}× · σ: {tp['stdev']:.1f}%</div>
        <div class="detail">P5–P95: [{tp['p5']:+.1f}%, {tp['p95']:+.1f}%] · range: [{tp['min']:+.1f}%, {tp['max']:+.1f}%]</div>
    </div>
    <div class="card">
        <h3>Total Memory Saved</h3>
        <div class="value {stat_class(s['total_mem_diff'])}">{humanize(s['total_mem_diff'])}</div>
        <div class="detail">sum across all {s['n_matches']} tests</div>
    </div>
    <div class="card">
        <h3>Total Time Change</h3>
        <div class="value {stat_class(s['total_time_diff'])}">{s['total_time_diff']:+.1f}s</div>
        <div class="detail">sum across all {s['n_matches']} tests</div>
    </div>
</div>

<h2>📊 Change Distribution</h2>
<div class="summary">
    <div class="card">
        <h3>Memory</h3>
        <div class="detail">🟢 Improved (&gt;{CHANGE_THRESHOLD}%): <strong>{mp['n_improved']}</strong> tests ({mp['n_improved']/max(mp['count'],1)*100:.0f}%)</div>
        <div class="detail">⚪ Unchanged (±{CHANGE_THRESHOLD}%): <strong>{mp['n_unchanged']}</strong> tests ({mp['n_unchanged']/max(mp['count'],1)*100:.0f}%)</div>
        <div class="detail">🔴 Regressed (&gt;{CHANGE_THRESHOLD}%): <strong>{mp['n_regressed']}</strong> tests ({mp['n_regressed']/max(mp['count'],1)*100:.0f}%)</div>
    </div>
    <div class="card">
        <h3>Time</h3>
        <div class="detail">🟢 Improved (&gt;{CHANGE_THRESHOLD}%): <strong>{tp['n_improved']}</strong> tests ({tp['n_improved']/max(tp['count'],1)*100:.0f}%)</div>
        <div class="detail">⚪ Unchanged (±{CHANGE_THRESHOLD}%): <strong>{tp['n_unchanged']}</strong> tests ({tp['n_unchanged']/max(tp['count'],1)*100:.0f}%)</div>
        <div class="detail">🔴 Regressed (&gt;{CHANGE_THRESHOLD}%): <strong>{tp['n_regressed']}</strong> tests ({tp['n_regressed']/max(tp['count'],1)*100:.0f}%)</div>
    </div>
</div>

<h2>🏋️ Heavy Tests Only (baseline &gt; 100 MiB, n={s['n_heavy']})</h2>
<div class="summary">
    <div class="card">
        <h3>Memory Change (median)</h3>
        <div class="value {stat_class(hm['median'])}">{hm['median']:+.1f}%</div>
        <div class="detail">mean: {hm['mean']:+.1f}% · geo mean: {hm['geo_mean']:.3f}× · σ: {hm['stdev']:.1f}%</div>
        <div class="detail">P5–P95: [{hm['p5']:+.1f}%, {hm['p95']:+.1f}%] · n={hm['count']}</div>
    </div>
    <div class="card">
        <h3>Time Change (median)</h3>
        <div class="value {stat_class(ht['median'])}">{ht['median']:+.1f}%</div>
        <div class="detail">mean: {ht['mean']:+.1f}% · geo mean: {ht['geo_mean']:.3f}× · σ: {ht['stdev']:.1f}%</div>
        <div class="detail">P5–P95: [{ht['p5']:+.1f}%, {ht['p95']:+.1f}%] · n={ht['count']}</div>
    </div>
</div>

<div class="note">
<strong>Note on measurement reliability:</strong> Memory values report the peak OCaml heap of the F* process,
excluding Z3 subprocesses. Time measurements are from single runs and may be noisy,
especially for tests completing in under 5 seconds.
Tests with baseline time &lt; 0.1s are excluded from time statistics.
The geometric mean (Geo Mean) of the patched/baseline ratio is the most robust summary statistic
for performance comparisons (1.0× = no change, &lt;1× = improvement).
</div>

<h2>📊 Distribution of Memory Changes (%)</h2>
<canvas id="histChart" height="250"></canvas>

<h2>📊 Memory: Baseline vs Patched</h2>
<canvas id="memChart" height="400"></canvas>

<h2>⏱️ Time: Baseline vs Patched</h2>
<canvas id="timeChart" height="400"></canvas>

<h2>📉 Top Memory Improvements</h2>
{table(by_mem_diff[:20])}

<h2>📈 Top Memory Regressions</h2>
{table(list(reversed(by_mem_diff[-20:])))}

<h2>⬇️ Top Time Improvements</h2>
{table(by_time_diff[:20])}

<h2>⬆️ Top Time Regressions</h2>
{table(list(reversed(by_time_diff[-20:])))}

<details><summary>Full Comparison ({s['n_matches']} tests)</summary>
{table(sorted(matches, key=lambda m: m['fn']), n=len(matches))}
</details>

<script>
const memData = {json.dumps(mem_data)};
const timeData = {json.dumps(time_data)};

// Filter to tests with significant memory (> 50 MiB)
const sigMem = memData.filter(d => d.base > 50 || d.patch > 50);
sigMem.sort((a,b) => b.base - a.base);

new Chart(document.getElementById('memChart'), {{
    type: 'scatter',
    data: {{
        datasets: [{{
            label: 'Tests (x=baseline, y=patched)',
            data: sigMem.map(d => ({{ x: d.base, y: d.patch }})),
            backgroundColor: sigMem.map(d => d.patch < d.base ? 'rgba(34,134,58,0.6)' : 'rgba(203,36,49,0.6)'),
            pointRadius: 5,
        }}, {{
            label: 'y = x (no change)',
            data: [{{x: 0, y: 0}}, {{x: Math.max(...sigMem.map(d=>d.base))*1.1, y: Math.max(...sigMem.map(d=>d.base))*1.1}}],
            type: 'line',
            borderColor: 'rgba(0,0,0,0.2)',
            borderDash: [5,5],
            pointRadius: 0,
            fill: false,
        }}]
    }},
    options: {{
        plugins: {{ tooltip: {{ callbacks: {{ label: (ctx) => sigMem[ctx.dataIndex]?.full || '' }} }} }},
        scales: {{
            x: {{ title: {{ display: true, text: 'Baseline Memory (MiB)' }} }},
            y: {{ title: {{ display: true, text: 'Patched Memory (MiB)' }} }}
        }}
    }}
}});

const sigTime = timeData.filter(d => d.base > 1 || d.patch > 1);
sigTime.sort((a,b) => b.base - a.base);

new Chart(document.getElementById('timeChart'), {{
    type: 'scatter',
    data: {{
        datasets: [{{
            label: 'Tests (x=baseline, y=patched)',
            data: sigTime.map(d => ({{ x: d.base, y: d.patch }})),
            backgroundColor: sigTime.map(d => d.patch < d.base ? 'rgba(34,134,58,0.6)' : 'rgba(203,36,49,0.6)'),
            pointRadius: 5,
        }}, {{
            label: 'y = x (no change)',
            data: [{{x: 0, y: 0}}, {{x: Math.max(...sigTime.map(d=>d.base))*1.1, y: Math.max(...sigTime.map(d=>d.base))*1.1}}],
            type: 'line',
            borderColor: 'rgba(0,0,0,0.2)',
            borderDash: [5,5],
            pointRadius: 0,
            fill: false,
        }}]
    }},
    options: {{
        plugins: {{ tooltip: {{ callbacks: {{ label: (ctx) => sigTime[ctx.dataIndex]?.full || '' }} }} }},
        scales: {{
            x: {{ title: {{ display: true, text: 'Baseline Time (s)' }} }},
            y: {{ title: {{ display: true, text: 'Patched Time (s)' }} }}
        }}
    }}
}});

// Memory change histogram
const histLabels = {json.dumps([f"{b}%" for b in hist_bins[:-1]])};
const histData = {json.dumps(hist_counts)};
new Chart(document.getElementById('histChart'), {{
    type: 'bar',
    data: {{
        labels: histLabels,
        datasets: [{{
            label: 'Number of tests',
            data: histData,
            backgroundColor: histData.map((_, i) => {{
                const b = {json.dumps(hist_bins)}[i];
                return b < 0 ? 'rgba(34,134,58,0.6)' : (b > 0 ? 'rgba(203,36,49,0.6)' : 'rgba(100,100,100,0.4)');
            }}),
        }}]
    }},
    options: {{
        plugins: {{ legend: {{ display: false }} }},
        scales: {{
            x: {{ title: {{ display: true, text: 'Memory Change (%)' }} }},
            y: {{ title: {{ display: true, text: 'Count' }} }}
        }}
    }}
}});
</script>
</body></html>"""
    return html

# ── Main ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Generate visual performance comparison from ramon files")
    parser.add_argument("lhs", help="Baseline directory with .ramon files")
    parser.add_argument("rhs", help="Patched directory with .ramon files")
    parser.add_argument("--output", "-o", default="report.html", help="Output file (default: report.html)")
    parser.add_argument("--format", "-f", choices=["html", "md"], default=None,
                        help="Output format (default: auto-detect from filename)")
    parser.add_argument("--lhs-label", default=None, help="Label for baseline")
    parser.add_argument("--rhs-label", default=None, help="Label for patched")
    args = parser.parse_args()

    # Auto-detect format from filename
    fmt = args.format
    if fmt is None:
        if args.output.endswith(".md"):
            fmt = "md"
        else:
            fmt = "html"

    lhs = args.lhs.rstrip("/")
    rhs = args.rhs.rstrip("/")

    print(f"Scanning {lhs} ...")
    f1 = find_ramon_files(lhs)
    print(f"  Found {len(f1)} .ramon files")

    print(f"Scanning {rhs} ...")
    f2 = find_ramon_files(rhs)
    print(f"  Found {len(f2)} .ramon files")

    matches, d1, d2 = make_matching(lhs, rhs, f1, f2)
    print(f"  Matched {len(matches)} tests")

    if not matches:
        print("No matching test results found!")
        sys.exit(1)

    st = compute_stats(matches)

    lhs_label = args.lhs_label or lhs
    rhs_label = args.rhs_label or rhs

    if fmt == "md":
        output = generate_markdown(matches, st, lhs_label, rhs_label)
    else:
        output = generate_html(matches, st, lhs_label, rhs_label)

    with open(args.output, "w") as f:
        f.write(output)

    print(f"\nReport written to {args.output} (format: {fmt})")
    print(f"\nSummary:")
    mp = st["mem_pct"]
    tp = st["time_pct"]
    hm = st["heavy_mem_pct"]
    ht = st["heavy_time_pct"]
    print(f"  All tests ({st['n_matches']}):")
    print(f"    Memory: median {mp['median']:+.1f}%, mean {mp['mean']:+.1f}%, geo mean {mp['geo_mean']:.3f}×, σ {mp['stdev']:.1f}%")
    print(f"            range [{mp['min']:+.1f}%, {mp['max']:+.1f}%], P5–P95 [{mp['p5']:+.1f}%, {mp['p95']:+.1f}%]")
    print(f"    Time:   median {tp['median']:+.1f}%, mean {tp['mean']:+.1f}%, geo mean {tp['geo_mean']:.3f}×, σ {tp['stdev']:.1f}%")
    print(f"            range [{tp['min']:+.1f}%, {tp['max']:+.1f}%], P5–P95 [{tp['p5']:+.1f}%, {tp['p95']:+.1f}%]")
    print(f"  Heavy tests ({st['n_heavy']}, baseline > 100 MiB):")
    print(f"    Memory: median {hm['median']:+.1f}%, mean {hm['mean']:+.1f}%, geo mean {hm['geo_mean']:.3f}×, σ {hm['stdev']:.1f}%")
    print(f"    Time:   median {ht['median']:+.1f}%, mean {ht['mean']:+.1f}%, geo mean {ht['geo_mean']:.3f}×, σ {ht['stdev']:.1f}%")
    print(f"  Distribution (mem): 🟢 {mp['n_improved']} improved, ⚪ {mp['n_unchanged']} unchanged, 🔴 {mp['n_regressed']} regressed")
    print(f"  Distribution (time): 🟢 {tp['n_improved']} improved, ⚪ {tp['n_unchanged']} unchanged, 🔴 {tp['n_regressed']} regressed")

if __name__ == "__main__":
    main()
