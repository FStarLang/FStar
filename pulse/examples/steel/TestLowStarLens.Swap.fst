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
module TestLowStarLens.Swap
open LowStar.Lens
open LowStar.Lens.Buffer
open LowStar.Lens.Tuple2
module B = LowStar.Buffer

(* This module illustrates a use of Low* lenses. When working with a
   fixed set of memory locations, lenses can provide a noticeable gain
   in abstraction.

   This "demo" show how to swap a pair of pointers and then to swap
   back and forth repeatedly. The punchline is that these proofs,
   being more abstract, scale significantly better than raw Low*
   proofs built on top of the Low* libraries (LowStar.Buffer,
   FStar.Monotonic.HyperStack, etc.).

   In fact, these proofs can be done on the "bare metal" logic
   provided by F* alone, i.e., you only need the definition of Tuple2
   in the SMT solver's context!
*)

(* Here's a simple swap *)
val swap (#a:_) (#b1 #b2:B.pointer a)
         (ps:tup2_t (ptr b1) (ptr b2))
  : LensST unit (lens_of ps)
    (requires fun _ -> True)
    (ensures (fun (v0, v1) _ (v0', v1') ->
       v0 == v1' /\
       v1 == v0'))
let swap (#a:_) #b1 #b2 ps =
  let v1 = read_fst ps 0ul in
  let v2 = read_snd ps 0ul in
  write_fst ps 0ul v2;
  write_snd ps 0ul v1

/// Here's the iterated swap, a glorified identity function
val n_swap (#a:_) (#b1 #b2:B.pointer a)
           (ps:tup2_t (ptr b1) (ptr b2))
  : LensST unit (lens_of ps)
    (requires fun _ -> True)
    (ensures (fun (v0, v1) _ (v0', v1') ->
       v0 == v0' /\
       v1 == v1'))

/// the proof of the implementation only needs FStar.Pervasives.Native
/// in scope
#reset-options "--using_facts_from 'FStar.Pervasives.Native'"
let n_swap #a #b1 #b2 ps =
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //40

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //80

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //120

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //160

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps; //180

    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;
    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps;    swap ps; swap ps  //200

#reset-options
/// The LensST effect is just a thin layer on top of the Stack effect
/// To call into LensST, we just need to package live, disjoint pointers
/// into a view, expose a bit of the abstraction, and call it
open FStar.HyperStack.ST
module LB = LowStar.Lens.Buffer
let call (p1 p2: B.pointer 'a)
  : Stack unit
    (requires fun h ->
      B.disjoint p1 p2 /\
      B.live h p1 /\
      B.live h p2)
    (ensures fun h0 _ h1 ->
      B.live h1 p1 /\
      B.live h1 p2 /\
      B.modifies (B.loc_union (B.loc_buffer p1)
                              (B.loc_buffer p2))
                 h0 h1 /\
      B.get h0 p1 0 == B.get h1 p1 0 /\
      B.get h0 p2 0 == B.get h1 p2 0)
  = let h0 = get () in
    //Creating the views
    let lp1 = LowStar.Lens.Buffer.mk p1 (ptr p1) h0 in
    let lp2 = LowStar.Lens.Buffer.mk p2 (ptr p2) h0 in
    let tup = LowStar.Lens.Tuple2.mk_tup2 lp1 lp2 in
    //Reveal some abstraction
    LowStar.Lens.Tuple2.elim_tup2_inv lp1 lp2;
    LowStar.Lens.Buffer.elim_inv lp1;
    LowStar.Lens.Buffer.elim_inv lp2;
    reveal_inv();
    //Make the call
    n_swap tup
