module Refinement.Generic.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module T = FStar.Tactics.Typeclasses

let get_t a b = a -> GTot b
let put_t a b = b -> a -> GTot a

/// `get_put`: The main useful law
/// You get what you put
let get_put (get:get_t 'a 'b) (put:put_t 'a 'b) =
  forall (a:'a) (b:'b).{:pattern (get (put b a))}
    get (put b a) == b

/// `put_get`: A law for eliminating redundant writes
/// Putting what you got is a noop
let put_get (get:get_t 'a 'b) (put:put_t 'a 'b) =
  forall (a:'a).{:pattern (put (get a) a)}
    put (get a) a == a

/// `put_put`: Another law for eliminating redundant writes
let put_put (get:get_t 'a 'b) (put:put_t 'a 'b) =
  forall (a:'a) (b1 b2:'b). {:pattern (put b2 (put b1 a))}
    put b2 (put b1 a) == put b2 a

noeq
type lens 'a 'b = {
  get: get_t 'a 'b;
  put: put_t 'a 'b;
  lens_laws: squash (
    get_put get put//  /\
    // put_get get put /\
    // put_put get put
  )
}

let imem inv = m:HS.mem{inv m}

let eloc = Ghost.erased B.loc
let l (x:eloc) : GTot B.loc = Ghost.reveal x
let get_reads_loc #b #inv (loc:eloc) (get:get_t (imem inv) b) =
  forall (h0 h1:imem inv) loc'.
    B.loc_disjoint (l loc) (l loc') /\
    B.modifies (l loc') h0 h1 ==>
    get h0 == get h1

let put_modifies_loc #b #inv (loc:eloc) (put:put_t (imem inv) b) =
  forall (h0:imem inv) (v:b).
    B.modifies (l loc) h0 (put v h0)

let invariant_reads_loc inv (loc:eloc) =
  forall h0 h1 loc'.
    inv h0 /\
    B.loc_disjoint (l loc) (l loc') /\
    B.modifies (l loc') h0 h1 ==>
    inv h1

let ih_lens inv b loc =
  l:lens (imem inv) b {
    get_reads_loc loc l.get /\
    put_modifies_loc loc l.put
  }


abstract
let mods fp snap (h:HS.mem) =
  B.modifies (l fp) snap h /\
  FStar.HyperStack.ST.equal_domains snap h

let reveal_mods ()
  : Lemma (forall fp snap h. {:pattern mods fp snap h}
            mods fp snap h <==>
            (B.modifies (l fp) snap h /\
             FStar.HyperStack.ST.equal_domains snap h))
  = ()

noeq
type hs_lens 'a 'b = {
  footprint: eloc;
  invariant: 'a -> HS.mem -> Type0;
  x:'a;
  snapshot:imem (invariant x);
  l:ih_lens (invariant x) 'b footprint;
  hs_lens_laws: squash (
    invariant_reads_loc (invariant x) footprint
  );
}

let snap (l:hs_lens 'a 'b) (h:imem (l.invariant l.x)) : hs_lens 'a 'b =
  {l with snapshot = h}
