#!/usr/bin/env python3
"""
Generate a detailed per-module breakdown from a bench_autopatterns run.

Usage:
  python3 tools/bench_autopatterns_report.py /tmp/bench-autopatterns-XXXX

Handles two layouts:
  base.stdout + head.stdout          (single-file from bench_autopatterns.sh)
  base/*.stdout + head/*.stdout      (per-target from older scripts)
"""
import sys, os, re, glob
from collections import defaultdict

if len(sys.argv) < 2:
    print(__doc__.strip()); sys.exit(1)
workdir = sys.argv[1]

def parse_wall(f):
    try:
        for line in open(f):
            m = re.search(r'wall clock.*?(\d+):(\d+\.\d+)', line)
            if m: return float(m.group(1))*60 + float(m.group(2))
    except: pass
    return 0

def find_files(workdir, label, ext):
    single = os.path.join(workdir, f'{label}.{ext}')
    if os.path.exists(single): return [single]
    sub = os.path.join(workdir, label)
    if os.path.isdir(sub): return sorted(glob.glob(os.path.join(sub, f'*.{ext}')))
    return []

def module_name(query_name):
    """Extract the module name from a query name like 'FStar.Seq.Properties.lemma_foo'.
    Module name = the uppercase-beginning dot-separated prefix."""
    parts = query_name.split('.')
    mod_parts = []
    for p in parts:
        if p and p[0].isupper():
            mod_parts.append(p)
        else:
            break
    return '.'.join(mod_parts) if mod_parts else query_name

def parse_query_stats(files):
    per_mod = defaultdict(lambda: dict(queries=0, rlimit=0.0, z3time=0))
    total = dict(queries=0, rlimit=0.0, z3time=0)
    for f in files:
        try:
            for line in open(f):
                m = re.search(
                    r'Query-stats \((\S+),.*?'
                    r'(succeeded|failed) in (\d+) milliseconds.*'
                    r'used rlimit ([\d.]+)', line)
                if m:
                    name = m.group(1)
                    ms = int(m.group(3))
                    rl = float(m.group(4))
                    total['queries'] += 1; total['rlimit'] += rl; total['z3time'] += ms
                    mod = module_name(name)
                    per_mod[mod]['queries'] += 1
                    per_mod[mod]['rlimit'] += rl
                    per_mod[mod]['z3time'] += ms
        except: pass
    return per_mod, total

def get_wall(workdir, label):
    return sum(parse_wall(f) for f in find_files(workdir, label, 'time'))

def pct(d, b): return d/b*100 if b else 0

base_mods, bt = parse_query_stats(find_files(workdir, 'base', 'stdout'))
head_mods, ht = parse_query_stats(find_files(workdir, 'head', 'stdout'))
bw = get_wall(workdir, 'base'); hw = get_wall(workdir, 'head')

# Summary
print("=" * 80)
print("  Auto-patterns benchmark: detailed breakdown")
print("=" * 80)
print()
print("%-20s %12s %12s %15s" % ("Metric", "Baseline", "Head", "Delta"))
print("-" * 65)
for lbl, bv, hv in [("Wall time (s)", bw, hw),
                      ("Z3 time (s)", bt['z3time']/1000, ht['z3time']/1000),
                      ("Z3 rlimit", bt['rlimit'], ht['rlimit'])]:
    print("%-20s %12.1f %12.1f %+10.1f (%+.1f%%)" % (lbl, bv, hv, hv-bv, pct(hv-bv, bv)))
dq = ht['queries'] - bt['queries']
print("%-20s %12d %12d %+10d (%+.1f%%)" % ("Queries", bt['queries'], ht['queries'], dq, pct(dq, bt['queries'])))

# Per-module breakdown
all_g = sorted(set(list(base_mods) + list(head_mods)))
zero = dict(queries=0, rlimit=0.0, z3time=0)
rows = []
for g in all_g:
    b = base_mods.get(g, zero); h = head_mods.get(g, zero)
    if b['queries'] == 0 and h['queries'] == 0: continue
    rows.append((g, b, h, h['rlimit'] - b['rlimit']))
rows.sort(key=lambda x: x[3])

print()
print("=" * 110)
print("  Per-module breakdown (sorted by rlimit delta)")
print("=" * 110)
print()
print("%-40s %6s %6s %7s  %9s %9s %10s  %8s %8s" % (
    "Module", "BQ", "HQ", "DQ", "BRlim", "HRlim", "DRlim(%)", "BZ3(s)", "HZ3(s)"))
print("-" * 110)
for g, b, h, drl in rows:
    print("%-40s %6d %6d %+7d  %9.1f %9.1f %+9.1f%%  %8.1f %8.1f" % (
        g[:40], b['queries'], h['queries'], h['queries']-b['queries'],
        b['rlimit'], h['rlimit'], pct(drl, b['rlimit']),
        b['z3time']/1000, h['z3time']/1000))
print("-" * 110)
print("%-40s %6d %6d %+7d  %9.1f %9.1f %+9.1f%%  %8.1f %8.1f" % (
    "TOTAL", bt['queries'], ht['queries'], ht['queries']-bt['queries'],
    bt['rlimit'], ht['rlimit'], pct(ht['rlimit']-bt['rlimit'], bt['rlimit']),
    bt['z3time']/1000, ht['z3time']/1000))
