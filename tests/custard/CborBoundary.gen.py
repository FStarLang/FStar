import sys, os, importlib.util

# The corpus and the model live in cbor-corpus/ and are shared with
# pulse/CborBoundarySlice.fst, which parses the same 48 vectors over a slice.
# There is exactly one copy of the vectors and one copy of the model, so the
# two checkers cannot drift into testing different things.
_here = os.path.dirname(os.path.abspath(__file__))
_corpus = os.path.join(_here, 'cbor-corpus')
_spec = importlib.util.spec_from_file_location(
    'cb_model', os.path.join(_corpus, 'model.py'))
model = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(model)

core = open(os.path.join(_here, 'CborBoundary.core.in')).read()
out = sys.argv[1]
vecfiles = (sys.argv[2].split(',') if len(sys.argv) > 2 else
            [os.path.join(_corpus, 'valid.txt'),
             os.path.join(_corpus, 'malformed.txt')])
vecs=[l.strip() for f in vecfiles for l in open(f) if l.strip()]
seen=set(); V=[]
for v in vecs:
    if v not in seen: seen.add(v); V.append(v)
o=['']
for i,v in enumerate(V):
    b=bytes.fromhex(v); chain='BNil'
    for x in reversed(b): chain='cons 0x%02Xuy (%s)'%(x,chain)
    o.append('let v%d () : ML blist = %s'%(i,chain))
o+=['','(* [check] is split into groups of 32 rather than one long [main]: a',
    '   single function with several hundred sequential statements roughly',
    '   doubles this module\'s verification time. *)',
    'let check (l : blist) (e : bool) (acc : ref bool) : ML unit =',
    '  let r = validate l in','  if r <> e then acc := false','']
CH=32; groups=[]
for g,start in enumerate(range(0,len(V),CH)):
    groups.append(g)
    o.append('let g%d (ok : ref bool) : ML unit ='%g)
    for i2 in range(start,min(start+CH,len(V))):
        o.append('  check (v%d ()) %s ok;'%(i2,'true' if model.validate(V[i2]) else 'false'))
    o+=['  ()','']
o.append('let main () : ML I32.t =')
o.append('  let ok = alloc true in')
for g in groups: o.append('  g%d ok;'%g)
o.append('  if !ok then 0l else 1l')
open(out,'w').write(core+'\n'.join(o)+'\n')
print(out,len(V),'vectors',len(groups),'groups')
