module Refinement.Generic.Tuple2
open Refinement.Generic.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open Refinement.Generic.Effect

let composable (l1:hs_lens 'a 'b) (l2:hs_lens 'c 'd) =
    B.all_disjoint [Ghost.reveal l1.footprint;
                    Ghost.reveal l2.footprint] /\
    l1.snapshot == l2.snapshot

let tup2 (l1 : hs_lens 'a 'b) (l2 : hs_lens 'c 'd) =
  hs_lens ('a & 'c) ('b & 'd)

//abstract
let mk #a1 #b1 (l1 : hs_lens a1 b1)
       #a2 #b2 (l2 : hs_lens a2 b2{composable l1 l2})
  : tup2 l1 l2
  = let fp =
      Ghost.hide (
        B.loc_union_l [Ghost.reveal l1.footprint;
                       Ghost.reveal l2.footprint
                      ])
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
    {
      footprint = fp;
      invariant = inv;
      x = x;
      l = l;
      snapshot = snap;
      hs_lens_laws = ();
    }

let snapped_op #a #b (lens:hs_lens a b) result pre post =
  s:imem (lens.invariant lens.x) ->
  RST result (snap lens s) pre post

let op_fst #a #b #c #d #result #pre #post
      (l1:hs_lens a b)
      (l2:hs_lens c d{composable l1 l2})
      (op:snapped_op l1 result pre post)
  : RST result (mk l1 l2)
    (requires fun (b0, d0) -> pre b0)
    (ensures fun (b0, d0) r (b1, d1) ->
      d0 == d1 /\
      post b0 r b1)
  = reveal_mods ();
    let s = FStar.HyperStack.ST.get () in
    op s

let op_snd #a #b #c #d #result #pre #post
      (l1:hs_lens a b)
      (l2:hs_lens c d{composable l1 l2})
      (op:snapped_op l2 result pre post)
  : RST result (mk l1 l2)
    (requires fun (b0, d0) -> pre d0)
    (ensures fun (b0, d0) r (b1, d1) ->
      b0 == b1 /\
      post d0 r d1)
  = reveal_mods ();
    let s = FStar.HyperStack.ST.get () in
    op s


let read_fst
      (l1:hs_lens 'a 'b)
      (l2:hs_lens 'c 'd{composable l1 l2})
      (r:reader_t l1)
 : RST 'b (mk l1 l2)
   (requires fun _ -> True)
   (ensures fun (b0, d0) b (b1, d1) ->
      d0 == d1 /\
      b == b1 /\
      b0 == b1)
  = reveal_mods();
    let s = FStar.HyperStack.ST.get () in
    r s

let write_fst
      (l1:hs_lens 'a 'b)
      (l2:hs_lens 'c 'd{composable l1 l2})
      (w:writer_t l1)
      (v:'b)
 : RST unit (mk l1 l2)
   (requires fun _ -> True)
   (ensures fun (b0, d0) _ (b1, d1) ->
      d0 == d1 /\
      v == b1)
  = reveal_mods();
    let s = FStar.HyperStack.ST.get() in
    w s v

let read_snd
      (l1:hs_lens 'a 'b)
      (l2:hs_lens 'c 'd{composable l1 l2})
      (r:reader_t l2)
 : RST 'd (mk l1 l2)
   (requires fun _ -> True)
   (ensures fun (b0, d0) d (b1, d1) ->
      d0 == d1 /\
      d == d1 /\
      b0 == b1)
  = reveal_mods();
    let s = FStar.HyperStack.ST.get () in
    r s

let write_snd
      (l1:hs_lens 'a 'b)
      (l2:hs_lens 'c 'd{composable l1 l2})
      (w:writer_t l2)
      (v:'d)
 : RST unit (mk l1 l2)
   (requires fun _ -> True)
   (ensures fun (b0, d0) _ (b1, d1) ->
      b0 == b1 /\
      v == d1)
  = reveal_mods();
    let s = FStar.HyperStack.ST.get() in
    w s v

let tup_inv #a1 #b1 (l1 : hs_lens a1 b1)
            #a2 #b2 (l2 : hs_lens a2 b2{composable l1 l2})
            (h:HS.mem)
  : Lemma (let l = mk l1 l2 in
           (l.invariant l.x h <==>
            l1.invariant l1.x h /\
            l2.invariant l2.x h) /\
           (l.invariant l.x h ==>
            Refinement.Generic.Effect.(
              get l h == (get l1 h, get l2 h))))
  = ()

module Ptr = Refinement.Generic.PointerLens

noeq
type ptr_pair 'a 'b =
  | PtrPair :
    #p1:B.pointer 'a ->
    pl1:Ptr.ptr_lens_rw p1 ->
    #p2:B.pointer 'b ->
    pl2:Ptr.ptr_lens_rw p2{
      composable (Ptr.lens_of_ptr pl1)
                 (Ptr.lens_of_ptr pl2)
    } ->
    ptr_pair 'a 'b

let mk_pair (p:ptr_pair 'a 'b) =
    mk (Ptr.lens_of_ptr p.pl1) (Ptr.lens_of_ptr p.pl2)

let get_fst (p:ptr_pair 'a 'b)
 : RST 'a (mk_pair p)
   (requires fun h -> True)
   (ensures fun (a0, b0) a (a1, b1) ->
     a0 == a1 /\
     b0 == b1 /\
      a == a1)
 = let (| l1, r1, _ |) = p.pl1 in
   read_fst l1
            (Ptr.lens_of_ptr p.pl2)
            r1

let get_snd (p:ptr_pair 'a 'b)
 : RST 'b (mk_pair p)
   (requires fun h -> True)
   (ensures fun (a0, b0) b (a1, b1) ->
     a0 == a1 /\
     b0 == b1 /\
      b == b1)
 = let (| l2, r2, _ |) = p.pl2 in
   read_snd (Ptr.lens_of_ptr p.pl1)
            l2
            r2

let set_fst (p:ptr_pair 'a 'b) (v:'a)
 : RST unit (mk_pair p)
   (requires fun h -> True)
   (ensures fun (a0, b0) _ (a1, b1) ->
      v == a1 /\
     b0 == b1)
 = let (| l1, _, w1 |) = p.pl1 in
   write_fst l1
            (Ptr.lens_of_ptr p.pl2)
            w1
            v

let set_snd (p:ptr_pair 'a 'b) (v:'b)
 : RST unit (mk_pair p)
   (requires fun h -> True)
   (ensures fun (a0, b0) _ (a1, b1) ->
     a0 == a1 /\
      v == b1)
 = let (| l2, _, w2 |) = p.pl2 in
   write_snd (Ptr.lens_of_ptr p.pl1)
             l2
             w2
             v
