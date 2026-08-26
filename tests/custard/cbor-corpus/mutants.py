import re, sys, os, subprocess, json
from concurrent.futures import ThreadPoolExecutor

# Mutation adequacy of the shared corpus, against whichever of the two
# checkers is named.  Usage:
#
#   python3 ../cbor-corpus/mutants.py [ops|consts] _output/CborBoundary.dc
#
# The prefix is derived from the basename of the .dc, and the parser
# functions to mutate are read from <Module>.parsers.txt next to the module.
# Mutating anything else -- the embedded vector constructors in particular --
# corrupts the test data rather than the parser and inflates the kill count.
FAMILY = sys.argv[1] if len(sys.argv) > 1 else 'ops'
SRC = sys.argv[2] if len(sys.argv) > 2 else '_output/CborBoundary.dc'
WORK = os.path.join(os.path.dirname(SRC) or '.', 'mutants')
MOD = os.path.basename(SRC)[:-len('.dc')]
PREFIX = MOD + '_'

_pl = os.path.join(os.path.dirname(os.path.abspath(SRC)), os.pardir,
                   MOD + '.parsers.txt')
PARSER = [PREFIX + l.strip() for l in open(_pl) if l.strip()
          and not l.startswith('#')]

lines = open(SRC).read().split('\n')

def ranges(ls):
    out = set()
    for i, l in enumerate(ls):
        if not l.endswith('{'):
            continue
        m = re.match(r'^[A-Za-z_][\w \*]*\b(' + PREFIX + r'\w+)\(', l)
        if not m or m.group(1) not in PARSER:
            continue
        depth = 0
        for j in range(i, len(ls)):
            depth += ls[j].count('{') - ls[j].count('}')
            out.add(j)
            if depth == 0 and j > i:
                break
    return out

rr = ranges(lines)
cnt = {}
for l in lines:
    cnt[l] = cnt.get(l, 0) + 1
body = [lines[i] for i in sorted(rr)]
uniq = [l for l in body if cnt[l] == 1 and len(l.strip()) >= 8]
print('parser body lines:', len(rr), 'unambiguous:', len(uniq))

if FAMILY == 'ops':
    subs = [(r'\bif \((.*?) < (.*?)\)', r'if (\1 <= \2)', 'lt->le'),
            (r'\bif \((.*?) <= (.*?)\)', r'if (\1 < \2)', 'le->lt'),
            (r'\bif \((.*?) == (.*?)\)', r'if (\1 != \2)', 'eq->ne'),
            (r'\breturn true;', 'return false;', 'true->false'),
            (r'\breturn false;', 'return true;', 'false->true')]
else:  # held-out: perturb the boundary constants themselves
    subs = [(r'\(\(uint8_t\)0x([0-9A-F]{2})U\)', None, 'byte+1'),
            (r'\b([0-9]+)ULL\b', None, 'ull+1'),
            (r'\b([0-9]+)UL\b', None, 'ul+1')]

cands = []
for l in uniq:
    for pat, rep, name in subs:
        if rep is None:
            m = re.search(pat, l)
            if not m:
                continue
            if name == 'byte+1':
                new = l[:m.start(1)] + '%02X' % ((int(m.group(1), 16) + 1) & 0xFF) + l[m.end(1):]
            else:
                new = l[:m.start(1)] + str(int(m.group(1)) + 1) + l[m.end(1):]
        else:
            if not re.search(pat, l):
                continue
            new = re.sub(pat, rep, l, count=1)
        if new != l:
            cands.append((l, new, name))

seen = set(); C = []
for c in cands:
    if c[:2] not in seen:
        seen.add(c[:2]); C.append(c)
print('mutants:', len(C))

os.makedirs(WORK, exist_ok=True)
# The mutant is written into WORK/, but the generated .c includes its own
# header by "" relative to where the extraction put it, so WORK/ is not
# enough: the header's directory has to be on the include path.
CC = ['cc', '-std=c11', '-w', '-fsanitize=address,undefined',
      '-fno-sanitize-recover=all',
      '-I' + (os.path.dirname(os.path.abspath(SRC)) or '.'), '-x', 'c']

def run(k):
    old, new, name = C[k]
    src = os.path.join(WORK, 'm%d.c' % k)
    exe = os.path.join(WORK, 'm%d.exe' % k)
    open(src, 'w').write('\n'.join(l.replace(old, new) if l == old else l for l in lines))
    r = subprocess.run(CC + [src, '-o', exe], capture_output=True)
    if r.returncode != 0:
        return (k, name, 'uncompilable')
    try:
        p = subprocess.run([exe], capture_output=True, timeout=60)
    except subprocess.TimeoutExpired:
        return (k, name, 'killed')
    return (k, name, 'killed' if p.returncode != 0 else 'survived')

with ThreadPoolExecutor(max_workers=64) as ex:
    res = list(ex.map(run, range(len(C))))

killed = sum(1 for _, _, s in res if s == 'killed')
surv = [(C[k][0].strip(), C[k][1].strip(), n) for k, n, s in res if s == 'survived']
bad = sum(1 for _, _, s in res if s == 'uncompilable')
print('family=%s  killed %d / %d  (uncompilable %d)' % (FAMILY, killed, len(C) - bad, bad))
for s in surv[:12]:
    print('  SURVIVED', s[2], '|', s[0][:80])
