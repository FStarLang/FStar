(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module LowStar.RST.TwoIndex

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open LowStar.Resource

(* Additional (currently assumed) lemmas: 
   [DA: Reasonable when addresses are not reused after deallocation, 
        but currently was not able to derive them from LowStar's buffers 
        library (Nik and/or Tahina will look into adding it to buffers library). 
        There are some other such assumed dotter around the RST development.] *)

assume val lemma_loc_not_unused_in_modifies (l0 l1:B.loc) (h0 h1:HS.mem)
  : Lemma (requires (B.loc_includes (B.loc_not_unused_in h0) l0 /\ 
                     B.loc_includes l1 l0 /\ B.modifies l1 h0 h1))
          (ensures  (B.loc_includes (B.loc_not_unused_in h1) l1))

assume val lemma_modifies_loc_disjoint (l0 l1:B.loc) (h0 h1 h2:HS.mem) 
  : Lemma (requires (B.modifies l0 h0 h1 /\
                     B.modifies l1 h1 h2 /\ 
                     (forall l . 
                       B.loc_disjoint l l0 /\ 
                       B.loc_includes (B.loc_not_unused_in h0) l 
                       ==> 
                       B.loc_disjoint l l1)))
          (ensures  (B.modifies l0 h0 h2))

assume val lemma_loc_disjoint_not_unused_in_modifies (h0 h1:HS.mem) (l l':B.loc)
  : Lemma (requires (B.loc_disjoint l' l /\ 
                     B.loc_includes (B.loc_not_unused_in h0) l' /\
                     B.modifies l h0 h1))
          (ensures  (B.loc_includes (B.loc_not_unused_in h1) l'))
          [SMTPat (B.loc_disjoint l' l);
           SMTPat (B.loc_includes (B.loc_not_unused_in h0) l');
           SMTPat (B.loc_includes (B.loc_not_unused_in h1) l')]

(*
// [DA: would be needed for scoped allocation of stack-allocated pointers]
assume val lemma_loc_not_unused_in_fresh_frame (l:B.loc) (h0 h1:HS.mem) 
  : Lemma (requires (B.loc_includes (B.loc_not_unused_in h0) l /\ HS.fresh_frame h0 h1))
          (ensures  (B.loc_includes (B.loc_not_unused_in h1) l)) 

assume val lemma_loc_not_unused_in_popped (l:B.loc) (h0 h1:HS.mem) 
  : Lemma (requires (B.loc_includes (B.loc_not_unused_in h0) l /\ HS.popped h0 h1))
          (ensures  (B.loc_includes (B.loc_not_unused_in h1) l)) 
*)

(* Abstract modifies clause for the resource-indexed state effect *)

abstract
let modifies (res0 res1:resource) (h0 h1:HS.mem) =
    B.modifies (as_loc (fp res0)) h0 h1 /\ 
    (forall frame . 
      B.loc_disjoint frame (as_loc (fp res0)) /\ 
      B.loc_includes (B.loc_not_unused_in h0) frame 
      ==> 
      B.loc_disjoint frame (as_loc (fp res1)) /\
      B.loc_includes (B.loc_not_unused_in h1) frame)

let modifies_refl (res:resource) (h:HS.mem) 
  : Lemma (modifies res res h h)
           [SMTPat (modifies res res h h)] =
  ()

let modifies_trans (res0 res1 res2:resource) (h0 h1 h2:HS.mem) 
  : Lemma (requires 
             modifies res0 res1 h0 h1 /\
             modifies res1 res2 h1 h2)
           (ensures
             modifies res0 res2 h0 h2)
           [SMTPat (modifies res0 res2 h0 h2);
            SMTPat (modifies res0 res1 h0 h1)] = 
  lemma_modifies_loc_disjoint (as_loc (fp res0)) (as_loc (fp res1)) h0 h1 h2
    
let reveal_modifies ()
  : Lemma (forall res0 res1 h0 h1.{:pattern modifies res0 res1 h0 h1}
             modifies res0 res1 h0 h1 <==>
             B.modifies (as_loc (fp res0)) h0 h1 /\
             (forall frame . 
               B.loc_disjoint frame (as_loc (fp res0)) /\ 
               B.loc_includes (B.loc_not_unused_in h0) frame 
               ==> 
               B.loc_disjoint frame (as_loc (fp res1)) /\
               B.loc_includes (B.loc_not_unused_in h1) frame))
  = ()

(* State effect indexed by resources *)

let r_pre (res:resource) = imem (inv res) -> Type0
let r_post res0 a res1 = imem (inv res0) -> x:a -> imem (inv (res1 x)) -> Type0

abstract
let rst_inv (res:resource) (h:HS.mem) =
  B.loc_includes (B.loc_not_unused_in h) (as_loc (fp res))

let reveal_rst_inv ()
  : Lemma (forall res h . 
             rst_inv res h 
             <==>
             B.loc_includes (B.loc_not_unused_in h) (as_loc (fp res)))
  = ()

// Monotonic WPs for RSTATE
let rstate_wp (a:Type) (res0:resource) (res1:a -> resource) = 
  wp:((x:a -> imem (inv (res1 x)) -> Type0) -> imem (inv res0) -> Type0){
      forall (p q:(x:a -> imem (inv (res1 x)) -> Type0)) h0 . (forall x h1 . p x h1 ==> q x h1) ==> wp p h0 ==> wp q h0
    }

effect RSTATE (a:Type)
              (res0:resource)                                   // Pre-resource (expected from the caller)
              (res1:a -> resource)                              // Post-resource (returned back to the caller)
              (wp:rstate_wp a res0 res1) =
       STATE a 
           (fun (p:a -> HS.mem -> Type)
              (h0:HS.mem) -> 
                inv res0 h0 /\                                  // Require the pre-resource invariant
                rst_inv res0 h0 /\                              // Require the additional footprints invariant
                wp (fun x h1 -> 
                     inv (res1 x) h1 /\                         // Ensure the post-resource invariant
                     rst_inv (res1 x) h1 /\                     // Ensure the additional footprints invariant
                     modifies res0 (res1 x) h0 h1 ==>           // Ensure that at most resources' footprints are modified
                     p x h1) h0)                                // Prove the continuation under this hypothesis

(* Pre- and postcondition style effect RST *)

effect RST (a:Type)
           (res0:resource)
           (res1:a -> resource)
           (pre:r_pre res0)
           (post:r_post res0 a res1) = 
       RSTATE a res0 res1 (fun p h0 -> 
         pre h0 /\ (forall x h1 . post h0 x h1 ==> p x h1))

(* Bind operation for RSTATE *)

let bind (#a #b:Type)
         (#res0:resource)
         (#res1:a -> resource)
         (#res2:b -> resource)
         (#wp0:rstate_wp a res0 res1)
         (#wp1:(x:a -> rstate_wp b (res1 x) res2))
         (f:unit -> RSTATE a res0 res1 wp0)
         (g:(x:a -> RSTATE b (res1 x) res2 (wp1 x)))
       : RSTATE b res0 res2 (fun p h0 -> wp0 (fun x h1 -> wp1 x p h1) h0) = 
  g (f ())

(* Generic framing operation for RSTATE (through resource inclusion) *)

// The pre- and post deltas are the same
let frame_post_delta (#outer0:resource)
                     (#inner0:resource)
                     (delta0:r_includes outer0 inner0)
                     (a:Type)
                     (outer1:a -> resource)
                     (inner1:a -> resource) =
  x:a -> delta1:r_includes (outer1 x) (inner1 x){delta0 == delta1}

let frame_wp (#outer0:resource)
          (#inner0:resource)
          (#a:Type)
          (#outer1:a -> resource)
          (#inner1:a -> resource)
          (delta0:r_includes outer0 inner0)
          (delta1:frame_post_delta delta0 a outer1 inner1)
          (wp:rstate_wp a inner0 inner1)
        : rstate_wp a outer0 outer1 =
  fun p h0 -> 
    wp (fun x (h1:imem (inv (inner1 x))) -> 
          inv (outer1 x) h1 /\
          sel (view_of delta0) h0 == sel (view_of (delta1 x)) h1 
          ==>
          p x h1) h0

let frame (#outer0:resource)
          (#inner0:resource)
          (#a:Type)
          (#outer1:a -> resource)
          (#inner1:a -> resource)
          (delta0:r_includes outer0 inner0)
          (delta1:frame_post_delta delta0 a outer1 inner1)
          (#wp:rstate_wp a inner0 inner1)
          ($f:unit -> RSTATE a inner0 inner1 wp)
        : RSTATE a outer0 outer1 (frame_wp delta0 delta1 wp) =
  reveal_view ();
  f ()
  
(* Generic framing operation for RST (through resource inclusion) *)

unfold
let frame_pre (#outer0:resource)
              (#inner0:resource)
              (delta0:r_includes outer0 inner0)
              (pre:r_pre inner0)
              (h:imem (inv outer0)) =
  pre h

unfold
let frame_post (#outer0:resource)
               (#inner0:resource)
               (#a:Type)
               (#outer1:a -> resource)
               (#inner1:a -> resource)
               (delta0:r_includes outer0 inner0)
               (delta1:frame_post_delta delta0 a outer1 inner1)
               (post:r_post inner0 a inner1)
               (h0:imem (inv outer0))
               (x:a)
               (h1:imem (inv (outer1 x))) = 
  delta0 == delta1 x /\ // here to trigger the refinement on (delta1 x)
  post h0 x h1 /\
  sel (view_of delta0) h0 == sel (view_of (delta1 x)) h1

// [DA: should be definable directly using RSTATE frame, but get 
//      an error about unexpected unification variable remaining]
let rst_frame (#outer0:resource)
              (#inner0:resource)
              (#a:Type)
              (#outer1:a -> resource)
              (#inner1:a -> resource)
              (delta0:r_includes outer0 inner0)
              (delta1:frame_post_delta delta0 a outer1 inner1)
              (#pre:r_pre inner0)
              (#post:r_post inner0 a inner1)
              ($f:unit -> RST a inner0 inner1 pre post)
            : RST a outer0 outer1 
                    (frame_pre delta0 pre) 
                    (frame_post delta0 delta1 post) =
  reveal_view ();
  let x = f () in 
  assert (delta0 == delta1 x); // here to trigger the refinement on (delta1 x)
  x
