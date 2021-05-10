(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Tactics.Effect

open FStar.Reflection.Types
open FStar.Tactics.Types
open FStar.Tactics.Result

(* This module is extracted, don't add any `assume val`s or extraction
 * will break. (`synth_by_tactic` is fine) *)

val ugh : unit

type wp_t0 (a:Type) = proofstate -> (__result a -> Type0) -> Type0

unfold
let monotonic (#a:Type) (wp:wp_t0 a) =
  forall ps p q. (forall x. p x ==> q x) ==> (wp ps p ==> wp ps q)

type wp_t (a:Type) = wp:wp_t0 a{monotonic wp}

type repr (a:Type) (wp:wp_t a) = ps:proofstate -> PURE (__result a) (wp ps)

unfold
let return_wp (#a:Type) (x:a) : wp_t a = fun ps p -> p (Success x ps)
let return (a:Type) (x:a) : repr a (return_wp x) = fun ps -> Success x ps

unfold
let g_bind (a:Type) (b:Type) (wp:wp_t a) (f:a -> wp_t b) : wp_t b =
  fun ps post ->
  wp ps (fun m' -> match m' with
                | Success a q -> f a q post
                | Failed e q -> post (Failed e q))
unfold
let g_compact (a:Type) (wp:wp_t a) : wp_t a =
    fun ps post -> forall k. (forall (r:__result a).{:pattern (guard_free (k r))} post r ==> k r) ==> wp ps k

#push-options "--admit_smt_queries true"
let bind (a b:Type)
  //(r1 r2:range)
  (wp1:wp_t a) (wp2:a -> wp_t b)
  (t1:repr a wp1) (t2:(x:a -> repr b (wp2 x)))
  : repr b (g_compact b (g_bind a b wp1 wp2)) =
  fun ps ->
  //let ps = set_proofstate_range ps (FStar.Range.prims_to_fstar_range r1) in
  let ps = incr_depth ps in
  let r = t1 ps in
  match r with
  | Success a ps' ->
    //let ps' = set_proofstate_range ps' (FStar.Range.prims_to_fstar_range r2) in
    // Force evaluation of __tracepoint q even on the interpreter
    begin match tracepoint ps' with
          | true -> t2 a (decr_depth ps')
    end
  | Failed e ps' -> Failed e ps'
#pop-options

let subcomp (a:Type) (wp1 wp2:wp_t a)
  (f:repr a wp1)
  : Pure (repr a wp2)
      (requires forall ps p. wp2 ps p ==> wp1 ps p)
      (ensures fun _ -> True)
  = f

unfold
let if_then_else_wp (#a:Type) (wp1 wp2:wp_t a) (b:bool) : wp_t a =
  fun ps p -> (b ==> wp1 ps p) /\
           ((~ b) ==> wp2 ps p)

let if_then_else (a:Type) (wp1 wp2:wp_t a)
  (f:repr a wp1) (g:repr a wp2)
  (b:bool)
  : Type =
  repr a (if_then_else_wp wp1 wp2 b)

reifiable
reflectable
effect {
  TAC (a:Type) (wp:wp_t a)
  with {repr; return; bind; subcomp; if_then_else}
}

effect TacH (a:Type) (pre:proofstate -> Type0) (post:proofstate -> __result a -> Type0) =
  TAC a (fun ps post' -> pre ps /\ (forall r. post ps r ==> post' r))

effect Tac (a:Type) = TacH a (requires fun _ -> True) (ensures fun _ _ -> True)

effect TacS (a:Type) = TacH a (requires fun _ -> True) (ensures fun _ r -> Success? r)

effect TacF (a:Type) = TacH a (requires fun _ -> False) (ensures fun _ _ -> True)

unfold
let lift_pure_tac_wp (#a:Type) (wp:pure_wp a) : wp_t a =
  FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun ps p -> wp (fun x -> p (Success x ps))

let lift_pure_tac (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp)
  : repr a (lift_pure_tac_wp wp)
  =  FStar.Monotonic.Pure.wp_monotonic_pure ();
     fun ps -> Success (f ()) ps

sub_effect PURE ~> TAC = lift_pure_tac

let get () : TAC proofstate (fun ps p -> p (Success ps ps)) =
  TAC?.reflect (fun ps -> Success ps ps)

let raise (#a:Type) (e:exn) : TAC a (fun ps p -> p (Failed #a e ps)) =
  TAC?.reflect (fun ps -> Failed #a e ps)


val with_tactic (t : unit -> Tac unit) (p:Type u#a) : Type u#a

(* This will run the tactic in order to (try to) produce a term of type
//  * t. Note that the type looks dangerous from a logical perspective. It
//  * should not lead to any inconsistency, however, as any time this term
//  * appears during typechecking, it is forced to be fully applied and the
//  * tactic is run. A failure of the tactic is a typechecking failure. It
//  * can be thought as a language construct, and not a real function. *)
val synth_by_tactic : (#t:Type) -> (unit -> Tac unit) -> Tot t

val assert_by_tactic (p:Type) (t:unit -> Tac unit)
  : Pure unit
         (requires (set_range_of (with_tactic t (squash p)) (range_of t)))
         (ensures (fun _ -> p))

(* We don't peel off all `with_tactic`s in negative positions, so give
//  * the SMT a way to reason about them *)
val by_tactic_seman : tau:(unit -> Tac unit) -> phi:Type -> Lemma (with_tactic tau phi ==> phi)
                                                                  [SMTPat (with_tactic tau phi)]

(* One can always bypass the well-formedness of metaprograms. It does
//  * not matter as they are only run at typechecking time, and if they get
//  * stuck, the compiler will simply raise an error. *)
let assume_safe (#a:Type) (tau:unit -> TacF a) : Tac a = admit (); tau ()

private let tac a b = a -> Tac b
private let tactic a = tac unit a

(* A hook to preprocess a definition before it is typechecked and
//  * elaborated. This attribute should be used for top-level lets. The
//  * tactic [tau] will be called on a quoting of the definition of the let
//  * (if many, once for each) and the result of the tactic will replace
//  * the definition. There are no goals involved, nor any proof obligation
//  * to be done by the tactic. *)
val preprocess_with (tau : term -> Tac term) : Tot unit

(* A hook to postprocess a definition, after typechecking, and rewrite
//  * it into a (provably equal) shape chosen by the user. This can be used
//  * to implement custom transformations previous to extraction, such as
//  * selective inlining. When ran added to a definition [let x = E], the
//  * [tau] metaprogram is presented with a goal of the shape [E == ?u] for
//  * a fresh uvar [?u]. The metaprogram should then both instantiate [?u]
//  * and prove the equality. *)
val postprocess_with (tau : unit -> Tac unit) : Tot unit

(* Similar semantics to [postprocess_with], but the metaprogram only
//  * runs before extraction, and hence typechecking and the logical
//  * environment should not be affected at all. *)
val postprocess_for_extraction_with (tau : unit -> Tac unit) : Tot unit

#set-options "--no_tactics"

val unfold_with_tactic (t:unit -> Tac unit) (p:Type)
  : Lemma (requires p)
          (ensures (with_tactic t p))

// let bind (a:Type) (b:Type) (t1:__tac a) (t2:a -> __tac b) : __tac b =
//     fun ps ->
//         let ps = set_proofstate_range ps (FStar.Range.prims_to_fstar_range r1) in
//         let ps = incr_depth ps in
//         let r = t1 ps in
//         match r with
//         | Success a ps' ->
//             let ps' = set_proofstate_range ps' (FStar.Range.prims_to_fstar_range r2) in
//             // Force evaluation of __tracepoint q even on the interpreter
//             begin match tracepoint ps' with
//             | true -> t2 a (decr_depth ps')
//             end
//         | Failed e ps' -> Failed e ps'





// private
// let __tac (a:Type) = proofstate -> M (__result a)

// (* monadic return *)
// private
// let __ret (a:Type) (x:a) : __tac a = fun (s:proofstate) -> Success x s

// (* monadic bind *)
// private
// let __bind (a b:Type)
//   //(r1 r2:range)
//   (wp1:wp_t a) (wp2:a -> wp_t b)
//   (t1:repr a wp1) (t2:(x:a -> repr b (wp2 x)))
//   : repr b ( =
//     fun ps ->
//         let ps = set_proofstate_range ps (FStar.Range.prims_to_fstar_range r1) in
//         let ps = incr_depth ps in
//         let r = t1 ps in
//         match r with
//         | Success a ps' ->
//             let ps' = set_proofstate_range ps' (FStar.Range.prims_to_fstar_range r2) in
//             // Force evaluation of __tracepoint q even on the interpreter
//             begin match tracepoint ps' with
//             | true -> t2 a (decr_depth ps')
//             end
//         | Failed e ps' -> Failed e ps'

// (* Actions *)
// private
// let __get () : __tac proofstate = fun s0 -> Success s0 s0

// private
// let __raise (a:Type0) (e:exn) : __tac a = fun (ps:proofstate) -> Failed #a e ps

// private
// let __tac_wp a = proofstate -> (__result a -> Tot Type0) -> Tot Type0

// (* The DMFF-generated `bind_wp` doesn't the contain the "don't
//  * duplicate the post-condition" optimization, which causes VCs (for
//  * well-formedness of tactics) to blow up.
//  *
//  * Plus, we don't need to model the ranges and depths: they make no
//  * difference since the proofstate type is abstract and the SMT never
//  * sees a concrete one.
//  *
//  * So, override `bind_wp` for the effect with an efficient one.
//  *)
// private
// unfold let g_bind (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) = fun ps post ->
//     wp ps (fun m' -> match m' with
//                      | Success a q -> f a q post
//                      | Failed e q -> post (Failed e q))

// private
// unfold let g_compact (a:Type) (wp:__tac_wp a) : __tac_wp a =
//     fun ps post -> forall k. (forall (r:__result a).{:pattern (guard_free (k r))} post r ==> k r) ==> wp ps k

// private
// unfold let __TAC_eff_override_bind_wp (r:range) (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) =
//     g_compact b (g_bind a b wp f)

// [@@ dm4f_bind_range ]
// new_effect {
//   TAC : a:Type -> Effect
//   with repr     = __tac
//      ; bind     = __bind
//      ; return   = __ret
//      ; __raise  = __raise
//      ; __get    = __get
// }

// (* Hoare variant *)
// effect TacH (a:Type) (pre : proofstate -> Tot Type0) (post : proofstate -> __result a -> Tot Type0) =
//     TAC a (fun ps post' -> pre ps /\ (forall r. post ps r ==> post' r))

// (* "Total" variant *)
// effect Tac (a:Type) = TacH a (requires (fun _ -> True)) (ensures (fun _ _ -> True))

// (* Metaprograms that succeed *)
// effect TacS (a:Type) = TacH a (requires (fun _ -> True)) (ensures (fun _ps r -> Success? r))

// (* A variant that doesn't prove totality (nor type safety!) *)
// effect TacF (a:Type) = TacH a (requires (fun _ -> False)) (ensures (fun _ _ -> True))

// unfold
// let lift_div_tac (a:Type) (wp:pure_wp a) : __tac_wp a =
//     fun ps p -> wp (fun x -> p (Success x ps))

// sub_effect DIV ~> TAC = lift_div_tac

// let get = TAC?.__get
// let raise (#a:Type) (e:exn) = TAC?.__raise a e

// val with_tactic (t : unit -> Tac unit) (p:Type u#a) : Type u#a

// (* This will run the tactic in order to (try to) produce a term of type
//  * t. Note that the type looks dangerous from a logical perspective. It
//  * should not lead to any inconsistency, however, as any time this term
//  * appears during typechecking, it is forced to be fully applied and the
//  * tactic is run. A failure of the tactic is a typechecking failure. It
//  * can be thought as a language construct, and not a real function. *)
// val synth_by_tactic : (#t:Type) -> (unit -> Tac unit) -> Tot t

// val assert_by_tactic (p:Type) (t:unit -> Tac unit)
//   : Pure unit
//          (requires (set_range_of (with_tactic t (squash p)) (range_of t)))
//          (ensures (fun _ -> p))

// (* We don't peel off all `with_tactic`s in negative positions, so give
//  * the SMT a way to reason about them *)
// val by_tactic_seman : tau:(unit -> Tac unit) -> phi:Type -> Lemma (with_tactic tau phi ==> phi)
//                                                                   [SMTPat (with_tactic tau phi)]

// (* One can always bypass the well-formedness of metaprograms. It does
//  * not matter as they are only run at typechecking time, and if they get
//  * stuck, the compiler will simply raise an error. *)
// let assume_safe (#a:Type) (tau:unit -> TacF a) : Tac a = admit (); tau ()

// private let tac a b = a -> Tac b
// private let tactic a = tac unit a

// (* A hook to preprocess a definition before it is typechecked and
//  * elaborated. This attribute should be used for top-level lets. The
//  * tactic [tau] will be called on a quoting of the definition of the let
//  * (if many, once for each) and the result of the tactic will replace
//  * the definition. There are no goals involved, nor any proof obligation
//  * to be done by the tactic. *)
// val preprocess_with (tau : term -> Tac term) : Tot unit

// (* A hook to postprocess a definition, after typechecking, and rewrite
//  * it into a (provably equal) shape chosen by the user. This can be used
//  * to implement custom transformations previous to extraction, such as
//  * selective inlining. When ran added to a definition [let x = E], the
//  * [tau] metaprogram is presented with a goal of the shape [E == ?u] for
//  * a fresh uvar [?u]. The metaprogram should then both instantiate [?u]
//  * and prove the equality. *)
// val postprocess_with (tau : unit -> Tac unit) : Tot unit

// (* Similar semantics to [postprocess_with], but the metaprogram only
//  * runs before extraction, and hence typechecking and the logical
//  * environment should not be affected at all. *)
// val postprocess_for_extraction_with (tau : unit -> Tac unit) : Tot unit

// #set-options "--no_tactics"

// val unfold_with_tactic (t:unit -> Tac unit) (p:Type)
//   : Lemma (requires p)
//           (ensures (with_tactic t p))
