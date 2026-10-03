import sys, os, importlib.util

# The corpus and the model live in ../cbor-corpus/ and are shared with
# ../CborBoundary.fst, which parses the same 48 vectors over a ref-linked
# list.  There is exactly one copy of the vectors and one copy of the model,
# so the two checkers cannot drift into testing different things.
_here = os.path.dirname(os.path.abspath(__file__))
_corpus = os.path.join(_here, os.pardir, 'cbor-corpus')
_spec = importlib.util.spec_from_file_location(
    'cbs_model', os.path.join(_corpus, 'model.py'))
model = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(model)

core = open(os.path.join(_here, 'CborBoundarySlice.core.in')).read()
out = sys.argv[1]
vecfiles = (sys.argv[2].split(',') if len(sys.argv) > 2 else
            [os.path.join(_corpus, 'valid.txt'),
             os.path.join(_corpus, 'malformed.txt')])
modname = sys.argv[3] if len(sys.argv) > 3 else 'CborBoundarySlice'

vecs = [l.strip() for f in vecfiles for l in open(f) if l.strip()]
seen = set(); V = []
for v in vecs:
    if v not in seen:
        seen.add(v); V.append(v)

o = ['']
for i, v in enumerate(V):
    b = bytes.fromhex(v)
    n = len(b)
    exp = 'true' if model.validate(v) else 'false'
    o.append('fn v%d ()' % i)
    o.append('  requires emp')
    o.append('  returns r : bool')
    o.append('  ensures emp')
    o.append('{')
    o.append('  let mut a = [| 0uy; %dsz |];' % n)
    o.append('  A.pts_to_len a;')
    o.append('  let s = S.from_array a %dsz;' % n)
    o.append('  S.pts_to_len s;')
    for j, x in enumerate(b):
        o.append('  put s %dsz 0x%02Xuy;' % (j, x))
    o.append('  let r = validate s;')
    o.append('  S.to_array s;')
    o.append('  (r = %s)' % exp)
    o.append('}')
    o.append('')

CH = 16
groups = []
for g, start in enumerate(range(0, len(V), CH)):
    groups.append(g)
    idx = list(range(start, min(start + CH, len(V))))
    o.append('fn g%d ()' % g)
    o.append('  requires emp')
    o.append('  returns r : bool')
    o.append('  ensures emp')
    o.append('{')
    for i2 in idx:
        o.append('  let x%d = v%d ();' % (i2, i2))
    o.append('  ' + ' && '.join('x%d' % i2 for i2 in idx))
    o.append('}')
    o.append('')

o.append('fn main ()')
o.append('  requires emp')
o.append('  returns r : FStar.Int32.t')
o.append('  ensures emp')
o.append('{')
for g in groups:
    o.append('  let y%d = g%d ();' % (g, g))
o.append('  if (' + ' && '.join('y%d' % g for g in groups) + ') { 0l } else { 1l }')
o.append('}')

body = '\n'.join(o) + '\n'
open(out, 'w').write(core.replace('module CborBoundarySlice', 'module ' + modname) + body)
print(out, len(V), 'vectors', len(groups), 'groups')
