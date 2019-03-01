module Refinement.Generic.PointerLens
open Refinement.Generic.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module T = FStar.Tactics.Typeclasses
open Refinement.Generic.Effect

let ptr_lens (p:B.pointer 'a) =
  l:hs_lens (B.pointer 'a) 'a{
    Ghost.reveal l.footprint == B.loc_buffer p
  }

let ptr_lens_rw (p:B.pointer 'a) =
  (l:ptr_lens p &
     reader_t l &
     writer_t l)

let lens_of_ptr (#p:B.pointer 'a)
                (prw:ptr_lens_rw p)
   : ptr_lens p
   = let (| l, _, _ |) = prw in l

let eloc_ptr (p:B.pointer 'a) : Tot eloc = Ghost.hide (B.loc_buffer p)

abstract
let mk (p:B.pointer 'a) (snap:HS.mem{B.live snap p})
  : Tot (l:ptr_lens_rw p{(lens_of_ptr l).snapshot == snap})
  = let plens : ptr_lens p =
        FStar.Classical.forall_intro_2 (B.g_upd_seq_as_seq p);
        let invariant (x:B.pointer 'a) (h:HS.mem) =
          B.live h x
        in
        let fp = eloc_ptr p in
        let get : get_t (imem (invariant p)) 'a =
          fun h -> B.get h p 0
        in
        let put : put_t (imem (invariant p)) 'a =
          fun v h -> B.g_upd p 0 v h
        in
        let l : ih_lens (invariant p) 'a fp = {
          get = get;
          put = put;
          lens_laws = ()
        }
        in
        {
          footprint = fp;
          invariant = invariant;
          x = p;
          snapshot = snap;
          l = l;
          hs_lens_laws = ()
        }
    in
    let reader : reader_t plens =
      fun s ->
        reveal_mods();
        B.index p 0ul
    in
    let writer : writer_t plens =
      fun s v ->
        reveal_mods();
        B.upd p 0ul v
    in
    (| plens, reader, writer |)

let elim_ptr_inv (#p:B.pointer 'a)
                 (prw:ptr_lens_rw p)
                 (h:HS.mem)
  : Lemma (let l = lens_of_ptr prw in
           (exists h'.{:pattern mk p h'} B.live h' p /\ prw == mk p h') /\
           l.invariant l.x h ==>
             B.live h p /\
             get l h == B.get h p 0)
  = ()
