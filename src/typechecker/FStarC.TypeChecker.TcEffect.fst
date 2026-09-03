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
module FStarC.TypeChecker.TcEffect
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Syntax
open FStarC.TypeChecker

open FStarC.Ident
open FStarC.Errors
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.TcTerm

module PC = FStarC.Parser.Const
module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module Env = FStarC.TypeChecker.Env
module N = FStarC.TypeChecker.Normalize
module TcUtil = FStarC.TypeChecker.Util
module Gen = FStarC.TypeChecker.Generalize
module TEQ = FStarC.TypeChecker.TermEqAndSimplify

open FStarC.Class.Show
open FStarC.Class.Tagged
open FStarC.Syntax.Print

(*
 * Typecheck the combinators of an effect definition.
 *
 * An effect definition plays no role in typechecking: it only gives the
 * effect an executable meaning, used by reification (extraction, tactics).
 * Still, we check that the combinators fit together, i.e. that
 *
 *   repr   : a:Type u#a -> Type u#r
 *   return : a:Type u#a -> a -> repr a
 *   bind   : a:Type u#a -> b:Type u#b -> repr a -> (a -> repr b) -> repr b
 *
 * (with [u#r] inferred) and we close over the universe variables by hand, so that the schemes have
 * exactly the number of universe parameters that reification expects.
 *)
(* Open the universe variables of a combinator scheme, or, if it has not been
   generalized yet (the common case: the surface syntax just mentions a name),
   invent [n] fresh ones.  Note that [tc_eff_decl] may run twice on the same
   declaration (two-phase checking), so we must be able to handle both. *)
let open_comb (r:Range.t) (n:int) (mname:lident) (name:string) (ts:S.tscheme) : ML (list univ_name & term) =
  let us, t = ts in
  if Nil? us
  then (if n = 1 then [S.new_univ_name (Some r)] else [S.new_univ_name (Some r); S.new_univ_name (Some r)]), t
  else if List.length us = n
  then SS.open_univ_vars us t
  else raise_error r Errors.Fatal_UnexpectedEffect
         (Format.fmt4 "The '%s' combinator of effect %s must be polymorphic in \
                       exactly %s universe(s), but it has %s"
            name (string_of_lid mname) (show n) (show (List.length us)))

let u_type (r:Range.t) (u:univ_name) : ML term = S.mk (Tm_type (U_name u)) r

(* [repr_app repr_ts u a] is [repr u#u a] *)
let repr_app (repr_ts:S.tscheme) (u:univ_name) (a:term) (r:Range.t) : ML term =
  let _, repr = Env.inst_tscheme_with repr_ts [U_name u] in
  S.mk_Tm_app repr [S.as_arg a] r

let check_comb env (us:list univ_name) (expected:term) (t:term) : ML S.tscheme =
  let env = Env.push_univ_vars env us in
  let t = tc_check_trivial_guard env t expected in
  us, SS.close_univ_vars us t

(* The [total] qualifier promises that computations in the effect terminate.
   For an effect with a representation this is checkable: if [repr a] is a
   function type, then it is the codomain of that function that carries the
   effect's own divergence. *)
let check_total_repr env (mname:lident) (repr_ts:S.tscheme) (r:Range.t) : ML unit =
  let us, _ = repr_ts in
  let u_a = List.hd us in
  let env = Env.push_univ_vars env us in
  let bv_a = S.new_bv (Some r) (u_type r u_a) in
  let env = Env.push_bv env bv_a in
  let t = repr_app repr_ts u_a (S.bv_to_name bv_a) r in
  let t = N.normalize [Env.Beta; Env.Eager_unfolding; Env.UnfoldUntil S.delta_constant] env t in
  let t = U.unascribe (SS.compress t) in
  match t.n with
  | Tm_arrow _ ->
    let _, c = U.arrow_formals_comp_ln t in
    if not (U.is_total_comp c) then
      raise_error r Errors.Fatal_UnexpectedEffect
        (Format.fmt2 "Effect %s is marked total, but its representation is a \
                      function into %s" (string_of_lid mname) (show (U.comp_effect_name c)))
  | _ -> ()

(* The universe of the representation, as a function of the universe of the
   result type: [[u_a]. Type u#r] where [repr u#u_a a : Type u#r].

   For a total effect this is the universe of the computation type itself,
   since [M t] is then inhabited by [repr t] -- see [Env.effect_universe].
   Reading it off [repr] once, here, saves re-deriving it at every arrow. *)
let repr_universe env (repr_ts:S.tscheme) (r:Range.t) : ML S.tscheme =
  let us, _ = repr_ts in
  let u_a = List.hd us in
  let env = Env.push_univ_vars env us in
  let bv_a = S.new_bv (Some r) (u_type r u_a) in
  let env = Env.push_bv env bv_a in
  let u = universe_of env (repr_app repr_ts u_a (S.bv_to_name bv_a) r) in
  [u_a], SS.close_univ_vars [u_a] (S.mk (Tm_type u) r)

let tc_eff_decl env (ed:S.eff_decl) (quals:list S.qualifier) (_attrs:list S.attribute) : ML S.eff_decl =
  match ed.combinators with
  | None -> ed
  | Some combs ->
    let r = range_of_lid ed.mname in
    let env0 = env in

    (* repr : a:Type u#a -> Type u#r, for some universe u#r inferred from
       the definition (typically u#a, or u#0 for a partial effect). *)
    let repr_ts =
      let us, t = open_comb r 1 ed.mname "repr" combs.repr in
      let u_a = List.hd us in
      let b_a = S.mk_binder (S.new_bv (Some r) (u_type r u_a)) in
      let t_r, _ = U.type_u () in
      let expected = U.arrow [b_a] (S.mk_Total t_r) in
      check_comb env0 us expected t in

    (* return : a:Type u#a -> a -> repr a *)
    let return_ts =
      let us, t = open_comb r 1 ed.mname "return" combs.return_repr in
      let u_a = List.hd us in
      let bv_a = S.new_bv (Some r) (u_type r u_a) in
      let a = S.bv_to_name bv_a in
      let expected =
        U.arrow [S.mk_binder bv_a; S.null_binder a]
                (S.mk_Total (repr_app repr_ts u_a a r)) in
      check_comb env0 us expected t in

    (* bind : a:Type u#a -> b:Type u#b -> repr a -> (a -> repr b) -> repr b *)
    let bind_ts =
      let us, t = open_comb r 2 ed.mname "bind" combs.bind_repr in
      let u_a, u_b = List.hd us, List.hd (List.tl us) in
      let bv_a = S.new_bv (Some r) (u_type r u_a) in
      let bv_b = S.new_bv (Some r) (u_type r u_b) in
      let a = S.bv_to_name bv_a in
      let b = S.bv_to_name bv_b in
      let repr_b = repr_app repr_ts u_b b r in
      let k = U.arrow [S.null_binder a] (S.mk_Total repr_b) in
      let expected =
        U.arrow [S.mk_binder bv_a; S.mk_binder bv_b;
                 S.null_binder (repr_app repr_ts u_a a r);
                 S.null_binder k]
                (S.mk_Total repr_b) in
      check_comb env0 us expected t in

    if List.contains S.TotalEffect quals then check_total_repr env0 ed.mname repr_ts r;

    { ed with combinators = Some { repr = repr_ts;
                                   return_repr = return_ts;
                                   bind_repr = bind_ts;
                                   repr_universe = repr_universe env0 repr_ts r } }

(*
 * A sub-effect declaration is an edge in the effect lattice, optionally
 * carrying a term-level lift used only for reification.
 *
 * A lift into an effect with representation [repr] has type
 *
 *   a:Type u#a -> (unit -> Msrc a) -> repr a
 *
 * or, when the source effect itself has a representation,
 *
 *   a:Type u#a -> src_repr a -> repr a
 *)
let tc_lift env (sub:S.sub_eff) (r:Range.t) : ML S.sub_eff =
  let _ = Env.get_effect_decl env sub.source in
  let ed_tgt = Env.get_effect_decl env sub.target in
  let lift =
    match sub.lift with
    | None ->
      (* No lift term.  If the target is reifiable, reification has to build the
         coercion itself, which it can only do by injecting a pure or divergent
         computation with the target's [return]. *)
      if Some? ed_tgt.combinators
      && not (U.is_pure_effect sub.source ||
              U.is_div_effect sub.source ||
              U.is_ghost_effect sub.source)
      then raise_error r Errors.Fatal_UnexpectedEffect
             (Format.fmt2 "Effect %s has a representation, so the lift from %s must be \
                           given explicitly: only a pure, ghost or divergent computation \
                           can be lifted with the target's return combinator"
                (string_of_lid sub.target) (string_of_lid sub.source));
      None
    | Some ts ->
      let repr_ts =
        match U.get_eff_repr ed_tgt with
        | Some repr -> repr
        | None ->
          raise_error r Errors.Fatal_UnexpectedEffect
            (Format.fmt1 "Effect %s has no representation, so it cannot be the \
                          target of a lift with a term" (string_of_lid sub.target)) in
      let us, t = open_comb r 1 sub.target "lift" ts in
      let u_a = List.hd us in
      let bv_a = S.new_bv (Some r) (u_type r u_a) in
      let a = S.bv_to_name bv_a in
      let src_arg =
        match Env.effect_decl_opt env sub.source with
        | Some (ed_src, _) when Some? ed_src.combinators ->
          repr_app (ed_src |> U.get_eff_repr |> Option.must) u_a a r
        | _ ->
          let c = S.mk_Comp ({ effect_name = sub.source;
                               result_typ = a;
                               flags = [];
                               source_effect_name = sub.source }) in
          U.arrow [S.null_binder S.t_unit] c in
      let expected =
        U.arrow [S.mk_binder bv_a; S.null_binder src_arg]
                (S.mk_Total (repr_app repr_ts u_a a r)) in
      Some (check_comb env us expected t) in
  { sub with lift }
