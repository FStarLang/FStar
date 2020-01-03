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
module MiniValeSemantics

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

/// 2^64
let pow2_64 = 0x10000000000000000

/// Natural numbers representable in 64 bits
type nat64 = i:int{0 <= i /\ i < pow2_64}

/// We have 4 registers
type reg = | Rax | Rbx | Rcx | Rdx

/// An operand is either a register or a constant
type operand =
  | OReg: r:reg -> operand
  | OConst: n:nat64 -> operand

/// Only 2 instructions here:
///   A move or an add
type ins =
  | Mov64: dst:operand -> src:operand -> ins
  | Add64: dst:operand -> src:operand -> ins

/// A program is
///   - a single instruction
///   - a block of instructions
///   - or a while loop
type code =
  | Ins: ins:ins -> code
  | Block: block:list code -> code
  | WhileLessThan: src1:operand -> src2:operand -> whileBody:code -> code

/// The state of a program is the register file
///    holiding a 64-bit value for each register
type state = reg -> nat64

/// fuel: To prove the termination of while loops, we're going to
/// instrument while loops with fuel
type fuel = nat

/// Evaluating an operand:
///   -- marked for reduction
///   -- Registers evaluated by state lookup
[@qattr]
let eval_operand (o:operand) (s:state) : nat64 =
  match o with
  | OReg r -> s r
  | OConst n -> n

/// updating a register state `s` at `r` with `v`
[@qattr]
let update_reg (s:state) (r:reg) (v:nat64) : state =
  fun r' -> if r = r' then v else s r'

/// updating a register state `s` at `r` with `s' r`
[@qattr]
let update_state (r:reg) (s' s:state) : state =
  update_reg s r (s' r)

// We don't have an "ok" flag, so errors just result an arbitrary state:
assume
val unknown_state (s:state) : state

(*** A basic semantics using
     a big-step interpreter
 ***)

/// Instruction evaluation:
///    only some operands are valid
let eval_ins (ins:ins) (s:state) : state =
  match ins with
  | Mov64 (OConst _) _ ->
    unknown_state s

  | Mov64 (OReg dst) src ->
    update_reg s dst (eval_operand src s)

  | Add64 (OConst _) _ ->
    unknown_state s

  | Add64 (OReg dst) src ->
    update_reg s dst ((s dst + eval_operand src s) % 0x10000000000000000)

/// eval_code:
///   A fueled big-step interpreter
///   While lops return None when we're out of fuel
let rec eval_code (c:code) (f:fuel) (s:state) : option state =
  match c with
  | Ins ins ->
    Some (eval_ins ins s)

  | Block cs ->
    eval_codes cs f s

  | WhileLessThan src1 src2 body ->
      if f = 0 then None
      else if eval_operand src1 s < eval_operand src2 s then
        match eval_code body f s with
        | None -> None
        | Some s -> eval_code c (f - 1) s
      else Some s

and eval_codes (cs:list code) (f:fuel) (s:state) : option state =
  match cs with
  | [] -> Some s
  | c::cs ->
      match eval_code c f s with
      | None -> None
      | Some s -> eval_codes cs f s

(*** END OF TRUSTED SEMANTICS ***)
////////////////////////////////////////////////////////////////////////////////


/// 1. We prove that incrasing the fuel is irrelevant to terminating executions

val increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires
    eval_code c f0 s0 == Some sN /\
    f0 <= fN)
  (ensures
    eval_code c fN s0 == Some sN)
  (decreases %[f0; c])

val increase_fuels (c:list code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires
    eval_code (Block c) f0 s0 == Some sN /\
    f0 <= fN)
  (ensures
    eval_code (Block c) fN s0 == Some sN)
  (decreases %[f0; c])

let rec increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) =
  match c with
  | Ins ins -> ()
  | Block l -> increase_fuels l s0 f0 sN fN
  | WhileLessThan src1 src2 body ->
      if eval_operand src1 s0 < eval_operand src2 s0 then
        match eval_code body f0 s0 with
        | None -> ()
        | Some s1 ->
            increase_fuel body s0 f0 s1 fN;
            increase_fuel c s1 (f0 - 1) sN (fN - 1)
      else ()
and increase_fuels (c:list code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) =
  match c with
  | [] -> ()
  | h::t ->
      let Some s1 = eval_code h f0 s0 in
      increase_fuel h s0 f0 s1 fN;
      increase_fuels t s1 f0 sN fN


/// 2. We can compute the fuel needed to run a sequential composition
///    as the max of the fuel to compute each piece of code in it
let lemma_merge (c:code) (cs:list code) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state)
  : Ghost fuel
  (requires
    eval_code c f0 s0 == Some sM /\
    eval_code (Block cs) fM sM == Some sN)
  (ensures fun fN ->
    eval_code (Block (c::cs)) fN s0 == Some sN)
  =
  let f = if f0 > fM then f0 else fM in
  increase_fuel c s0 f0 sM f;
  increase_fuel (Block cs) sM fM sN f;
  f

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
/////////////////////////////////////////////////////////////////
[@qattr]
let t_post = state -> Type0

[@qattr]
let t_pre = state -> Type0

/// t_wp: The type of weakest preconditions
let t_wp = t_post -> t_pre

/// c `has_wp` wp: The main judgment in our program logic
let has_wp (c:code) (wp:t_wp) : Type =
  k:t_post -> //for any post-condition
  s0:state -> //and initial state
  Ghost (state * fuel)
    (requires wp k s0) //Given the precondition
    (ensures fun (sM, f0) -> //we can compute the fuel f0 needed so that
      eval_code c f0 s0 == Some sM /\  //eval_code with that fuel returns sM
      k sM) //and the post-condition is true on sM

/// An abbreviation for a thunked lemma
let t_lemma (pre:Type0) (post:Type0) =
  unit -> Lemma (requires pre) (ensures post)


/// `with_wp` : A typeclass for code packaged with its wp
[@qattr]
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
   pre:Type0 ->
   post:Type0 ->
   t_lemma pre post ->
   with_wps cs ->
   with_wps cs

[@qattr]
let rec vc_gen (cs:list code) (qcs:with_wps cs) (k:t_post)
  : Tot (state -> Tot Type0 (decreases qcs))
  =
  fun s0 ->
  match qcs with
  | QEmpty ->
    k s0 //no instructions; prove the postcondition right away

  | QSeq qc qcs ->
    // let pre_tl = //compute the VC generator for the tail, a precondition
    qc.wp (vc_gen (Cons?.tl cs) qcs k) s0
    // in
    // qc.wp pre_tl s0 //apply the wp-generator to the precondition for the tail

  | QLemma pre post _ qcs ->
    pre /\ //prove the precondition of the lemma
    (post ==> vc_gen cs qcs k s0) //and assume its postcondition to verify the progra

/// The vc-generator is sound
let rec vc_sound (cs:list code)
                 (qcs:with_wps cs)
                 (k:state -> Type0)
                 (s0:state)
  : Ghost (state * fuel)
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
let lemma_Move (s0:state) (dst:operand) (src:operand)
  : Ghost (state * fuel)
  (requires OReg? dst)
  (ensures fun (sM, fM) ->
    eval_code (Ins (Mov64 dst src)) fM s0 == Some sM /\
    eval_operand dst sM == eval_operand src s0 /\
    sM == update_state (OReg?.r dst) sM s0
  )
  =
  let Some sM = eval_code (Ins (Mov64 dst src)) 0 s0 in
  (sM, 0)

[@qattr]
let wp_Move (dst:operand) (src:operand) (k:state -> Type0) (s0:state) : Type0 =
  OReg? dst /\
  (forall (x:nat64).
    let sM = update_reg s0 (OReg?.r dst) x in
    eval_operand dst sM == eval_operand src s0 ==> k sM
  )

let hasWp_Move (dst:operand) (src:operand) (k:state -> Type0) (s0:state) : Ghost (state * fuel)
  (requires wp_Move dst src k s0)
  (ensures fun (sM, f0) -> eval_code (Ins (Mov64 dst src)) f0 s0 == Some sM /\ k sM)
  =
  lemma_Move s0 dst src

[@qattr]
let inst_Move (dst:operand) (src:operand) : with_wp (Ins (Mov64 dst src)) =
  QProc (Ins (Mov64 dst src)) (wp_Move dst src) (hasWp_Move dst src)

////////////////////////////////////////////////////////////////////////////////
//Instance for Add
////////////////////////////////////////////////////////////////////////////////
let lemma_Add (s0:state) (dst:operand) (src:operand) : Ghost (state * fuel)
  (requires OReg? dst /\ eval_operand dst s0 + eval_operand src s0 < pow2_64)
  (ensures fun (sM, fM) ->
    eval_code (Ins (Add64 dst src)) fM s0 == Some sM /\
    eval_operand dst sM == eval_operand dst s0 + eval_operand src s0 /\
    sM == update_state (OReg?.r dst) sM s0
  )
  =
  let Some sM = eval_code (Ins (Add64 dst src)) 0 s0 in
  (sM, 0)

[@qattr]
let wp_Add (dst:operand) (src:operand) (k:state -> Type0) (s0:state) : Type0 =
  OReg? dst /\ eval_operand dst s0 + eval_operand src s0 < pow2_64 /\
  (forall (x:nat64).
    let sM = update_reg s0 (OReg?.r dst) x in
    eval_operand dst sM == eval_operand dst s0 + eval_operand src s0 ==> k sM
  )

let hasWp_Add (dst:operand) (src:operand) (k:state -> Type0) (s0:state) : Ghost (state * fuel)
  (requires wp_Add dst src k s0)
  (ensures fun (sM, f0) -> eval_code (Ins (Add64 dst src)) f0 s0 == Some sM /\ k sM)
  =
  lemma_Add s0 dst src

[@qattr]
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
  ]

unfold
let normal (x:Type0) : Type0 =
  norm [nbe; iota; zeta; simplify; primops; delta_attr [`%qattr]; delta_only normal_steps] x

let vc_sound_norm
     (cs:list code)
     (qcs:with_wps cs)
     (k:state -> Type0)
     (s0:state)
  : Ghost (state * fuel)
    (requires
      normal (vc_gen cs qcs k s0))
    (ensures fun (sN, fN) ->
      eval_code (Block cs) fN s0 == Some sN /\ k sN)
  = vc_sound cs qcs k s0

////////////////////////////////////////////////////////////////////////////////
// Verifying a simple program
////////////////////////////////////////////////////////////////////////////////

[@qattr]
let codes_Triple : list code =
  [Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//1
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//2
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//3
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//4
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//5
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//6
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//7
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//8
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//9
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//10
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//11
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//1
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//2
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//3
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//4
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//5
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//6
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//7
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//8
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//9
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//10
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//11
Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//1
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//2
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//3
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//4
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//5
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//6
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//7
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//8
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//9
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//10
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//11
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//1
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//2
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//3
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//4
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//5
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//6
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//7
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//8
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//9
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//10
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//11
Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//1
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//2
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//3
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//4
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//5
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//6
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//7
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//8
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//9
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//10
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//11
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//1
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//2
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//3
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//4
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//5
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//6
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//7
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//8
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//9
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//10
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
   Ins (Mov64 (OReg Rbx) (OReg Rax));   //mov rbx rax;
//11
   Ins (Add64 (OReg Rax) (OReg Rbx));   //add rax rbx;
   Ins (Add64 (OReg Rbx) (OReg Rax))]   //add rbx rax

[@qattr]
let inst_Triple : with_wps codes_Triple = //A typeclass instance for our program
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (
  QSeq (inst_Move (OReg Rbx) (OReg Rax)) (

  QSeq (inst_Add (OReg Rax) (OReg Rbx)) (
  QSeq (inst_Add (OReg Rbx) (OReg Rax)) (
  QEmpty))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
open FStar.FunctionalExtensionality
open FStar.Mul

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

[@qattr]
let state_eq (s0 s1:state) : Ghost Type0
  (requires True)
  (ensures fun b -> b ==> s0 `feq` s1)
  =
  s0 Rax == s1 Rax /\
  s0 Rbx == s1 Rbx /\
  s0 Rcx == s1 Rcx /\
  s0 Rdx == s1 Rdx

#reset-options
// let lemma_Triple (s0:state)
//   : Ghost (state & fuel)
//     (requires
//       s0 Rax < 100)
//     (ensures fun (sM, f0) ->
//       eval_code (Block codes_Triple) f0 s0 == Some sM /\
//       sM Rbx == 3 * s0 Rax /\
//       sM `feq` update_state Rax sM (update_state Rbx sM s0)) =
// // Naive proof:
//   let b1 = codes_Triple in
//   let (s2, fc2) = lemma_Move s0 (OReg Rbx) (OReg Rax) in let b2 = Cons?.tl b1 in
//   let (s3, fc3) = lemma_Add s2 (OReg Rax) (OReg Rbx) in  let b3 = Cons?.tl b2 in
//   let (s4, fc4) = lemma_Add s3 (OReg Rbx) (OReg Rax) in  let b4 = Cons?.tl b3 in
//   let (sM, f4) = (s4, 0) in
//   let f3 = lemma_merge (Cons?.hd b3) b4 s3 fc4 s4 f4 sM in
//   let f2 = lemma_merge (Cons?.hd b2) b3 s2 fc3 s3 f3 sM in
//   let fM = lemma_merge (Cons?.hd b1) b2 s0 fc2 s2 f2 sM in
//   (sM, fM)

#push-options "--profile_component FStar.TypeChecker --profile MiniValeSemantics"
let lemma_Triple_opt (s0:state)
  : Ghost (state & fuel)
    (requires
      s0 Rax < 100)
    (ensures fun (sM, f0) ->
      eval_code (Block codes_Triple) f0 s0 == Some sM /\
      sM Rbx == 3 * s0 Rax /\
      sM `feq` update_state Rax sM (update_state Rbx sM s0)) =
  // Optimized VC generation:
  vc_sound_norm
    codes_Triple
    inst_Triple
    (fun sM -> sM Rbx == 3 * s0 Rax /\ state_eq sM (update_state Rax sM (update_state Rbx sM s0)))
    s0
