(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.VCUtil

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Ident
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print {}
open FStarC.TypeChecker.CommonBase
open FStarC.TypeChecker.Env
open FStarC.Class.Show
module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module BU = FStarC.Util
module C = FStarC.Parser.Const
module Env = FStarC.TypeChecker.Env

let dbg_Simplification = Debug.get_toggle "Simplification"

let label reason r f : ML term =
    mk (Tm_meta {tm=f; meta=Meta_labeled(reason, r, false)}) f.pos

(* A type with at most one inhabitant: [unit] and any refinement of it,
   including [squash p].  An equation [x == e] at such a type is vacuous, and
   recording it would drag [e] -- a whole [calc] chain, say -- into the context
   of every obligation that follows. *)
let rec is_unit_like (t:term) : ML bool =
  let t = SS.compress t in
  if U.is_unit t then true
  else match t.n with
       | Tm_refine {b} -> is_unit_like b.sort
       | _ -> Some? (U.un_squash t)

(* A match on a scrutinee the solver cannot reduce.
 *
 * Such a term is a dead end for an equation [x == e]: the solver can take
 * nothing out of it, exactly as for an irreducible head symbol (condition (c)
 * of [should_return]).  Whatever the branches do establish is already recorded
 * in the match's result type by [combine_branch_res_typs], and that type is in
 * scope wherever the equation would be.
 *
 * Restating it is not merely useless but expensive: a match is ascribed with
 * its own result type (see [mk_match] in TcTerm), so a type that mentions a
 * nested match mentions that match's type too, and the two grow into each
 * other -- doubling at every level of nesting.
 *)
let rec is_stuck_match (e:term) : ML bool =
  match (SS.compress (U.unmeta e)).n with
  | Tm_ascribed {tm} -> is_stuck_match tm
  | Tm_match {scrutinee} ->
    let hd, _ = U.head_and_args_full scrutinee in
    (match (U.un_uinst (SS.compress (U.unmeta hd))).n with
     (* A constructor or a literal scrutinee does pick a branch, so the match
        reduces and the equation is worth stating. *)
     | Tm_fvar fv -> None? fv.fv_qual
     | Tm_constant _ -> false
     | _ -> true)
  | _ -> false

(* should_return env (Some e) lc:
 * We will "return" e, adding an equality to the VC, if all of the following conditions hold
 * (a) e is a pure or ghost term
 * (b) Its return type, (U.comp_result lc), is not a sub-singleton (unit, squash, etc), if (U.comp_result lc) is an arrow, then we check the comp type of the arrow
 *     An exception is made for reifiable effects -- they are useful even if they return unit -- except when it is an layered effect, we never return layered effects
 * (c) Its head symbol is not marked irreducible (in this case inlining is not going to help, it is equivalent to having a bound variable)
 * (d) It does not mention a name bound by the [let rec] being checked, since such a name cannot appear in a type that outlives it
 * (e) It is not a match the solver cannot reduce (see [is_stuck_match])
 *)
let should_return env eopt lc : ML _ =
  let lc_is_unit_or_effectful =
    //if (U.comp_result lc) is not an arrow, arrow_formals_comp returns Tot (U.comp_result lc)
    let c = (U.comp_result lc) |> U.arrow_formals_comp |> snd in
    if U.is_pure_or_ghost_comp c
    then c |> U.comp_result |> N.unfold_whnf env |> U.is_unit
    else true
  in

  match eopt with
  | None -> false //no term to return
  | Some e ->
    U.is_pure_or_ghost_comp lc           &&  //condition (a), (see above)
    not lc_is_unit_or_effectful                &&  //condition (b)
    (let head, _ = U.head_and_args_full e in
     match (U.un_uinst head).n with
     | Tm_fvar fv ->  not (Env.is_irreducible env (lid_of_fv fv))  //condition (c)
     | _ -> true)                                                  &&
    not (Env.mentions_rec_name env e) &&    //condition (d), see [Env.mentions_rec_name]
    not (is_stuck_match e)                  //condition (e)

(*
 * e has type lc, and lc is either pure or ghost
 * This function refines lc's result type with [_ == e].
 *
 * There is no postcondition to record [result == e] in any more, so we state it
 * as a refinement of the result type instead.  This matters for a value
 * returned out of an effectful computation -- [let x = f (g y) in ...] with [f]
 * effectful and [g] pure -- where nothing else relates [x] to [g y].
 *)
let assume_result_eq_pure_term_in_m env (m_opt:option lident) (e:term) (lc:comp) : ML comp =
  let t = (U.comp_result lc) in
  if is_unit_like t then lc
  else
    let u_t = env.universe_of env t in
    let x = S.new_bv (Some t.pos) t in
    let eq = U.mk_eq2 u_t t (S.bv_to_name x) e in
    U.set_result_typ lc (U.refine x eq)

let maybe_assume_result_eq_pure_term_in_m env (m_opt:option lident) (e:term) (lc:comp) : ML comp =
  if not (should_return env (Some e) lc) then lc
  else assume_result_eq_pure_term_in_m env m_opt e lc

let maybe_assume_result_eq_pure_term env e lc : ML _ =
  maybe_assume_result_eq_pure_term_in_m env None e lc

(* Having already seen_args to head (from right to left),
   compute the guard, if any, for the next argument,
   if head is a short-circuiting operator *)
let short_circuit (head:term) (seen_args:args) : ML guard_formula =
    let short_bin_op (f: term -> ML guard_formula) : args -> ML guard_formula = function
        | [] -> (* no args seen yet *) Trivial
        | [(fst, _)] -> f fst
        | _ -> failwith "Unexpected args to binary operator" in

    let op_and_e e = U.b2t e   |> NonTrivial in
    let op_or_e e  = U.mk_neg (U.b2t e) |> NonTrivial in
    let op_and_t t = t |> NonTrivial in
    let op_or_t t  = t |> U.mk_neg |> NonTrivial in
    let op_imp_t t = t |> NonTrivial in

    let short_op_ite : args -> ML guard_formula = function
        | [] -> Trivial
        | [(guard, _)] -> NonTrivial guard
        | [_then;(guard, _)] -> U.mk_neg guard |> NonTrivial
        | _ -> failwith "Unexpected args to ITE" in
    let table : list (lident & (args -> ML guard_formula)) =
        [(C.op_And,  short_bin_op op_and_e);
         (C.op_Or,   short_bin_op op_or_e);
         (C.and_lid, short_bin_op op_and_t);
         (C.or_lid,  short_bin_op op_or_t);
         (C.imp_lid, short_bin_op op_imp_t);
         (C.ite_lid, short_op_ite);] in

     match head.n with
        | Tm_fvar fv ->
          let lid = fv.fv_name in
          begin match BU.find_map table (fun (x, mk) -> if lid_equals x lid then Some (mk seen_args) else None) with
            | None ->   Trivial
            | Some g -> g
          end
        | _ -> Trivial

let short_circuit_head l : ML _ =
    let hd, _ = U.head_and_args_full l in
    match (U.un_uinst hd).n with
        | Tm_fvar fv ->
           BU.for_some (S.fv_eq_lid fv)
                   [C.op_And;
                    C.op_Or;
                    C.and_lid;
                    C.or_lid;
                    C.imp_lid;
                    C.ite_lid]
        | _ -> false

(* Deciding when it's okay to issue an SMT query for
 * equating a term whose head symbol is `head` with another term
 *
 * NB: this function only uses env for checking delta_depths,
 * so it's fine to use wl.tcenv.
 *)
let rec may_relate_by_smt env is_eq head : ML _
  =
    match (SS.compress head).n with
    | Tm_name _
    | Tm_match _ -> true
    | Tm_fvar fv ->
      (match Env.delta_depth_of_fv env fv with
       | Delta_equational_at_level _ ->
         true
       | Delta_abstract _ ->
         //these may be relatable via a logical theory
         //which may provide **equations** among abstract symbols
         //Note, this is specifically not applicable for subtyping queries: see issue #1359
         is_eq
       | _ -> false)
    | Tm_ascribed {tm=t}
    | Tm_uinst (t, _)
    | Tm_meta {tm=t} -> may_relate_by_smt env is_eq t
    | _ -> false

(* This function is also called by tactics, and should not drop the guards
under [admit] (like simplify_guard does). *)
let simplify_vc full_norm_allowed env t : ML _
  =
  Stats.record "simplify_vc" fun () ->
  if !dbg_Simplification then
    Format.print1 "Simplifying guard %s\n" (show t);
  let steps = [Env.Beta;
               Env.Eager_unfolding;
               Env.Simplify;
               Env.Primops;
               Env.Exclude Env.Zeta] in
  let steps = if full_norm_allowed then steps else Env.NoFullNorm::steps in
  let t' =
    Profiling.profile
      (fun () -> N.normalize steps env t)
      (Some (Ident.string_of_lid (Env.current_module env)))
      "FStarC.TypeChecker.Rel.simplify_vc"
  in
  if !dbg_Simplification then
    Format.print1 "Simplified guard to %s\n" (show t');
  t'
