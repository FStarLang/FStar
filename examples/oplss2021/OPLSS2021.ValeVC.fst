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

   Authors: C. Hawblitzel, N. Swamy
*)
module OPLSS2021.ValeVC
open OPLSS2021.Vale
open FStar.FunctionalExtensionality
open FStar.Mul

/////////////////////////////////////////////////////////////////
// Now, we're going to define a verification-condition generator
//
// The main idea is that we're going to:
//
//   1. define a kind of typeclass, that associates with a
//      piece of code a weakest-precondition rule for it
//
//   2. Define a WP-generator that computes WPs for each of the
//      control constructs of the language, given a program
//      represented as the raw code packaged with their typeclass
//      instances for computing their WPs
//
//   3. Run the WP generator on F*'s normalizer and feed to Z3
//      the resulting verification condition
/////////////////////////////////////////////////////////////////

(*
This is a highly-simplified model of Vale/F*, based on Section
3.1-3.3 of the paper of the POPL '19 paper.

It is derived from the QuickRegs1 code in the popl-artifact-submit
branch of Vale.
*)


/// We use this tag to mark certain definitions
/// and control normalization based on it
irreducible
let qattr = ()

[@@qattr]
let t_post = state -> prop

[@@qattr]
let t_pre = state -> prop

/// t_wp: The type of weakest preconditions
let t_wp = t_post -> t_pre

/// c `has_wp` wp: The main judgment in our program logic
let has_wp (c:code) (wp:t_wp) : Type =
  k:t_post -> //for any post-condition
  s0:state -> //and initial state
  Pure (state & fuel)
    (requires wp k s0) //Given the precondition
    (ensures fun (sM, f0) -> //we can compute the fuel f0 needed so that
      eval_code c f0 s0 == Some sM /\  //eval_code with that fuel returns sM
      k sM) //and the post-condition is true on sM

/// An abbreviation for a thunked lemma
let t_lemma (pre:prop) (post:prop) =
  unit -> Lemma (requires pre) (ensures post)

/// `with_wp` : A typeclass for code packaged with its wp
[@@qattr]
noeq
type with_wp : code -> Type =
| QProc: c:code -> wp:t_wp -> hasWp:has_wp c wp -> with_wp c

/// `with_wps`: A typclass for lists of code values packages with their wps
noeq
type with_wps : list code -> Type =
| QEmpty: //empty list
   with_wps []

| QSeq:   //cons
   #c:code ->
   #cs:list code ->
   hd:with_wp c ->
   tl:with_wps cs ->
   with_wps (c::cs)

| QLemma: //augmenting an instruction sequence with a lemma
   #cs:list code ->
   pre:prop ->
   post:prop ->
   t_lemma pre post ->
   with_wps cs ->
   with_wps cs

[@@qattr]
let rec vc_gen (cs:list code) (qcs:with_wps cs) (k:t_post)
  : Tot (state -> Tot prop (decreases qcs))
  =
  fun s0 ->
  match qcs with
  | QEmpty ->
    k s0 //no instructions; prove the postcondition right away

  | QSeq qc qcs ->
    qc.wp (vc_gen (Cons?.tl cs) qcs k) s0

  | QLemma pre post _ qcs ->
    pre /\ //prove the precondition of the lemma
    (post ==> vc_gen cs qcs k s0) //and assume its postcondition to verify the progra

/// The vc-generator is sound
let rec vc_sound (cs:list code)
                 (qcs:with_wps cs)
                 (k:state -> prop)
                 (s0:state)
  : Pure (state & fuel)
    (requires vc_gen cs qcs k s0)
    (ensures fun (sN, fN) -> eval_code (Block cs) fN s0 == Some sN /\ k sN)
  = match qcs with
    | QEmpty -> (s0, 0)
    | QSeq qc qcs ->
      let Cons c cs' = cs in
      let (sM, fM) = qc.hasWp (vc_gen cs' qcs k) s0 in
      let (sN, fN) = vc_sound cs' qcs k sM in
      let fN' = lemma_merge c cs' s0 fM sM fN sN in
      (sN, fN')
    | QLemma pre post lem qcs' ->
      lem ();
      vc_sound cs qcs' k s0

let vc_sound' (cs:list code) (qcs:with_wps cs)
  : has_wp (Block cs) (vc_gen cs qcs)
  = vc_sound cs qcs

(*** Instances of with_wp ***)


////////////////////////////////////////////////////////////////////////////////
//Instance for Mov
////////////////////////////////////////////////////////////////////////////////
[@@qattr]
let wp_Move (dst:operand) (src:operand) (k:state -> prop) (s0:state)
  : prop
  = OReg? dst /\
    (forall (x:nat64).
      let sM = update_reg s0 (OReg?.r dst) x in
      eval_operand dst sM == eval_operand src s0 ==> k sM
    )

let hasWp_Move (dst:operand) (src:operand) (k:state -> prop) (s0:state)
  : Pure (state & fuel)
    (requires wp_Move dst src k s0)
    (ensures fun (sM, f0) -> eval_code (Ins (Mov64 dst src)) f0 s0 == Some sM /\ k sM)
  = lemma_Move s0 dst src

[@@qattr]
let inst_Move (dst:operand) (src:operand) : with_wp (Ins (Mov64 dst src)) =
  QProc (Ins (Mov64 dst src)) (wp_Move dst src) (hasWp_Move dst src)

////////////////////////////////////////////////////////////////////////////////
//Instance for Add
////////////////////////////////////////////////////////////////////////////////
[@@qattr]
let wp_Add (dst:operand) (src:operand) (k:state -> prop) (s0:state) : prop =
  OReg? dst /\ eval_operand dst s0 + eval_operand src s0 < pow2_64 /\
  (forall (x:nat64).
    let sM = update_reg s0 (OReg?.r dst) x in
    eval_operand dst sM == eval_operand dst s0 + eval_operand src s0 ==> k sM
  )

let hasWp_Add (dst:operand) (src:operand) (k:state -> prop) (s0:state)
  : Pure (state & fuel)
    (requires wp_Add dst src k s0)
    (ensures fun (sM, f0) -> eval_code (Ins (Add64 dst src)) f0 s0 == Some sM /\ k sM)
  = lemma_Add s0 dst src

[@@qattr]
let inst_Add (dst:operand) (src:operand) : with_wp (Ins (Add64 dst src)) =
  QProc (Ins (Add64 dst src)) (wp_Add dst src) (hasWp_Add dst src)

////////////////////////////////////////////////////////////////////////////////
//Running the VC generator using the F* normalizer
////////////////////////////////////////////////////////////////////////////////
unfold
let normal_steps : list string =
  [
    `%OReg?;
    `%OReg?.r;
    `%QProc?.wp;
    `%eval_operand;
    `%update_reg;
    `%update_state;
  ]

unfold
let normal (x:Type0) : Type0 =
  norm [nbe;
        iota;
        zeta;
        simplify;
        primops;
        delta_attr [`%qattr];
        delta_only normal_steps] x

let vc_sound_norm
     (cs:list code)
     (qcs:with_wps cs)
     (k:state -> prop)
     (s0:state)
  : Pure (state & fuel)
    (requires
      normal (vc_gen cs qcs k s0))
    (ensures fun (sN, fN) ->
      eval_code (Block cs) fN s0 == Some sN /\ k sN)
  = vc_sound cs qcs k s0

////////////////////////////////////////////////////////////////////////////////
// Verifying a simple program
////////////////////////////////////////////////////////////////////////////////

[@@qattr]
let inst_Triple : with_wps codes_Triple = //A typeclass instance for our program
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Add (OReg Rax) (OReg Rbx)) (
  QSeq (inst_Add (OReg Rbx) (OReg Rax)) (
  QEmpty)))


(*
procedure Triple()
    modifies rax; rbx;
    requires rax < 100;
    ensures rbx == 3 * old(rax);
{
    Mov(rbx, rax);
    Add(rax, rbx);
    Add(rbx, rax);
}
*)

[@@qattr]
let state_eq (s0 s1:state) : Pure Type0
  (requires True)
  (ensures fun b -> b ==> s0 `feq` s1)
  =
  s0 Rax == s1 Rax /\
  s0 Rbx == s1 Rbx /\
  s0 Rcx == s1 Rcx /\
  s0 Rdx == s1 Rdx

let lemma_Triple_opt (s0:state)
  : Pure (state & fuel)
    (requires
      s0 Rax < 100)
    (ensures fun (sM, f0) ->
      eval_code (Block codes_Triple) f0 s0 == Some sM /\
      sM Rbx == 3 * s0 Rax /\
      sM `feq` update_state Rbx sM (update_state Rax sM s0))
   =
  // Optimized VC generation:
  vc_sound_norm
    codes_Triple
    inst_Triple
    (fun sM -> sM Rbx == 3 * s0 Rax /\ state_eq sM (update_state Rax sM (update_state Rbx sM s0)))
    s0
