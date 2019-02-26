module Refinement.Generic.Comp
open Refinement.Generic

let pair_inv #r1 (inv1:inv_t r1)
             #r2 (inv2:inv_t r2)
   : inv_t (r1 & r2)
   = fun h (r1, r2) -> 
       inv1 h r1 /\
       inv2 h r2

assume 
val pair (#r1:Type) (#inv1:inv_t r1) (#a1:Type) (l1:lens inv1 a1)
         (#r2:Type) (#inv2:inv_t r2) (#a2:Type) (l2:lens inv2 a2)
   : lens (pair_inv inv1 inv2) (a1 & a2) 
module HS = FStar.HyperStack

assume
val pair_get (#r1:Type) (#inv1:inv_t r1) (#a1:Type) (l1:lens inv1 a1) 
             (#r2:Type) (#inv2:inv_t r2) (#a2:Type) (l2:lens inv2 a2)
   : Lemma (forall (s1:r1) (s2:r2) (h:HS.mem{pair_inv inv1 inv2 h (s1, s2)}).
                 {:pattern  l_get (pair l1 l2) (s1, s2) h }
                 l_get (pair l1 l2) (s1, s2) h ==
                 (l_get l1 s1 h, l_get l2 s2 h))

let pair_rlens 
         (#r1:Type) (#inv1:inv_t r1) (#a1:Type) (#l1:lens inv1 a1)
         (#r2:Type) (#inv2:inv_t r2) (#a2:Type) (#l2:lens inv2 a2)
         (a:rlens l1) (b:rlens l2)
  : rlens (pair l1 l2)
  = a , b

module HST = FStar.HyperStack.ST

let frame (#a:Type)
         (#roots1:Type u#1)
         (#inv1:inv_t roots1)
         (#b1:Type0)
         (#l1:lens inv1 b1)
         (#r1:rlens l1)
         (#pre: b1 -> Type) 
         (#post: b1 -> a -> b1 -> Type) 
         (#roots2:Type u#1)
         (#inv2:inv_t roots2)
         (#b2:Type0)
         (#l2:lens inv2 b2)
         (#r2:rlens l2)
         ($f: unit -> RST a r1 pre post)
  : RST a (pair_rlens r1 r2)
    (requires fun (b0, _) ->
      pre b0)
    (ensures fun (b0, b1) a (b0', b1') ->
      post b0 a b0' /\
      b1 == b1')
  = let h0 = HST.get () in
    pair_get l1 l2;
    let v = f () in
    let h1 = HST.get () in
    assume (inv2 h1 r2);
    assume (l_get l2 r2 h0 ==
            l_get l2 r2 h1);
    v            

module B = LowStar.Buffer
assume 
val atomic_lens (b:Type)
  : lens #(B.pointer b) (fun (h:HS.mem) (ptr:B.pointer b) -> True /\ B.live h ptr) b
let atomic_rlens (#b:Type) (ptr:B.pointer b) : rlens (atomic_lens b) = ptr

let with_fresh (#a:Type)
               (#roots1:Type u#1)
               (#inv1:inv_t roots1)
               (#b1:Type0)
               (#l1:lens inv1 b1)
               (#r1:rlens l1)
               (#b2:Type)
               (#pre: (b1 * b2) -> Type)
               (#post:(b1 * b2) -> a -> (b1 * b2) -> Type)
               (v:b2)
               (f: (r2:rlens (atomic_lens b2) ->
                   RST a (pair_rlens r1 r2) 
                     (requires (fun (s1, s2) ->
                       pre (s1, s2)))
                     (ensures (fun (s1, s2) x (s1', s2') ->
                       post (s1, s2) x (s1', s2')))))
  : RST a r1 
    (requires fun s1 -> pre (s1, v))
    (ensures (fun s1 x s1' ->
      exists v'. post (s1, v) x (s1', v')))
  = admit()
