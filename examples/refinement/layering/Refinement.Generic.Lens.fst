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

let get_reads_loc #b #inv (loc:B.loc) (get:get_t (imem inv) b) =
  forall (h0 h1:imem inv) loc'.
    B.loc_disjoint loc loc' /\
    B.modifies loc' h0 h1 ==>
    get h0 == get h1

let put_modifies_loc #b #inv (loc:B.loc) (put:put_t (imem inv) b) =
  forall (h0:imem inv) (v:b).
    B.modifies loc h0 (put v h0)

let invariant_reads_loc inv (loc:B.loc) =
  forall h0 h1 loc'.
    inv h0 /\
    B.loc_disjoint loc loc' /\
    B.modifies loc' h0 h1 ==>
    inv h1

let ih_lens inv b loc =
  l:lens (imem inv) b {
    get_reads_loc loc l.get /\
    put_modifies_loc loc l.put
  }


abstract
let mods fp snap h0 h1 =
  (B.modifies fp snap h0 ==>
   B.modifies fp snap h1) /\
  B.modifies fp h0 h1

let st_get_t #a #b #fp #inv (x:a) (l:ih_lens (inv x) b fp) =
  unit ->
  Stack b
  (requires inv x)
  (ensures (fun h0 b h1 ->
    h0 == h1 /\
    b == l.get h0))

let st_put_t #a #b (#fp:B.loc) #inv (x:a) (snap:imem (inv x)) (l:ih_lens (inv x) b fp) =
  v:b ->
  Stack unit
  (requires fun h0 ->
    inv x h0)
  (ensures (fun h0 _ h1 ->
    inv x h1 /\
    mods fp snap h0 h1 /\
    v == l.get h1))

noeq
type hs_lens 'a 'b = {
  footprint: B.loc;
  invariant: 'a -> HS.mem -> Type0;
  x:'a;
  snapshot:imem (invariant x);
  l:ih_lens (invariant x) 'b footprint;
  st_get:st_get_t x l;
  st_put:st_put_t x snapshot l;
  hs_lens_laws: squash (
    invariant_reads_loc (invariant x) footprint
  );
}


let tup2 #a1 #b1 (l1 : hs_lens a1 b1)
         #a2 #b2 (l2 : hs_lens a2 b2{
             l1.snapshot == l2.snapshot /\
             B.all_disjoint [l1.footprint;
                             l2.footprint;
                            ]})
  : GTot (hs_lens (a1 & a2) (b1 & b2))
  = let fp =
      B.loc_union_l [l1.footprint;
                     l2.footprint
                     ]
    in
    let inv (a, b) h : prop =
      l1.invariant a h /\
      l2.invariant b h
    in
    let x = l1.x, l2.x in
    let snap : imem (inv x) = l1.snapshot in
    let get : get_t (imem (inv x)) (b1 & b2) =
      fun h ->
        l1.l.get h,
        l2.l.get h
      in
    let put : put_t (imem (inv x)) (b1 & b2) =
      fun (v1, v2) h ->
         l2.l.put v2
        (l1.l.put v1 h)
    in
    let l : ih_lens (inv x) (b1 & b2) fp =
      {
        get = get;
        put = put;
        lens_laws = ()
      }
    in
    let st_get : st_get_t x l =
      fun () ->
        let v1 = l1.st_get () in
        let v2 = l2.st_get () in
        v1, v2
    in
    let st_put : st_put_t x snap l =
      fun (v1, v2) ->
        l1.st_put v1;
        l2.st_put v2
    in
    {
      footprint = fp;
      invariant = inv;
      x = x;
      l = l;
      snapshot = snap;
      st_get=st_get;
      st_put=st_put;
      hs_lens_laws = ();
    }

let tup3 #a1 #b1 (l1 : hs_lens a1 b1)
         #a2 #b2 (l2 : hs_lens a2 b2)
         #a3 #b3 (l3 : hs_lens a3 b3{
             l1.snapshot == l2.snapshot /\
             l2.snapshot == l3.snapshot /\
             B.all_disjoint [l1.footprint;
                             l2.footprint;
                             l3.footprint
                            ]})
  : GTot (hs_lens (a1 & a2 & a3) (b1 & b2 & b3))
  = let fp =
      B.loc_union_l [l1.footprint;
                     l2.footprint;
                     l3.footprint
                     ]
    in
    let inv (a, b, c) h : prop =
      l1.invariant a h /\
      l2.invariant b h /\
      l3.invariant c h
    in
    let x = l1.x, l2.x, l3.x in
    let snap : imem (inv x) = l1.snapshot in
    let get : get_t (imem (inv x)) (b1 & b2 & b3) =
      fun h ->
        l1.l.get h,
        l2.l.get h,
        l3.l.get h
      in
    let put : put_t (imem (inv x)) (b1 & b2 & b3) =
      fun (v1, v2, v3) h ->
         l3.l.put v3
        (l2.l.put v2
        (l1.l.put v1 h))
    in
    let l : ih_lens (inv x) (b1 & b2 & b3) fp =
      {
        get = get;
        put = put;
        lens_laws = ()
      }
    in
    let st_get : st_get_t x l =
      fun () ->
        let v1 = l1.st_get () in
        let v2 = l2.st_get () in
        let v3 = l3.st_get () in
        v1, v2, v3
    in
    let st_put : st_put_t x snap l =
      fun (v1, v2, v3) ->
        l1.st_put v1;
        l2.st_put v2;
        l3.st_put v3
    in
    {
      footprint = fp;
      invariant = inv;
      x = x;
      l = l;
      snapshot = snap;
      st_get=st_get;
      st_put=st_put;
      hs_lens_laws = ();
    }

let ptr_lens (p:B.pointer 'a) (snap:HS.mem{B.live snap p})
  : GTot (hs_lens (B.pointer 'a) 'a)
  = let invariant (x:B.pointer 'a) (h:HS.mem) =
      B.live h x
    in
    let fp = B.loc_buffer p in
    let get : get_t (imem (invariant p)) 'a =
      fun h -> B.get h p 0
    in
    let put : put_t (imem (invariant p)) 'a =
      fun v h ->
        let h1 = B.g_upd p 0 v h in
        B.g_upd_seq_as_seq p (Seq.upd (B.as_seq h p) 0 v) h;
        h1
    in
    assume (get_put get put);
    assume (put_modifies_loc fp put);
    let l : ih_lens (invariant p) 'a fp = {
         get = get;
         put = put;
         lens_laws = ()
      }
    in
    let st_get : st_get_t p l =
      fun () -> B.index p 0ul
    in
    let st_put : st_put_t p snap l =
      fun v -> B.upd p 0ul v
    in
    {
      footprint = fp;
      invariant = invariant;
      x = p;
      snapshot = snap;
      l = l;
      st_get = st_get;
      st_put = st_put;
      hs_lens_laws = ()
    }
