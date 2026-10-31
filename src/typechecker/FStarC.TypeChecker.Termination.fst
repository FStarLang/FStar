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
module FStarC.TypeChecker.Termination

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Errors
open FStarC.TypeChecker
open FStarC.TypeChecker.Env
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Util
open FStarC.Class.Show
open FStarC.Syntax.Print {}
module S  = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U  = FStarC.Syntax.Util
module N  = FStarC.TypeChecker.Normalize
module BU = FStarC.Util
module Const = FStarC.Parser.Const
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
module VCUtil = FStarC.TypeChecker.VCUtil

(* Is [t] the type of a precondition, i.e. a [squash]?

   Asked of a binder's sort on every application, so answer it syntactically
   where possible: [ToSyntax.desugar_comp] emits a literal [Prims.squash], and
   running [unfold_whnf] over the proposition just to learn that is wasted work.
   The normalizing fallback is only for a precondition stated through an
   abbreviation. *)
let is_squash_typ env (t:typ) : ML bool =
  Some? (U.un_squash t) ||
  Some? (U.un_squash (N.unfold_whnf env t))

let guard_letrecs (inst_univs:bool) env actuals expected_c : ML (list (lbname&typ&univ_names)) =
    match env.letrecs with
    | [] -> []
    | letrecs ->
      let r = Env.get_range env in
      let env = {env with letrecs=[]} in

      (* An implicit binder of squash type is the image of a precondition
         (see [ToSyntax.desugar_comp]): it is proof-irrelevant, so it can
         neither carry the termination measure nor be part of one. *)
      let is_precondition_binder env (b:binder) : ML bool =
        Some? b.binder_qual
        && Implicit? (Some?.v b.binder_qual)
        && is_squash_typ env b.binder_bv.sort
      in

      let decreases_clause bs c =
          if Debug.low ()
          then Format.print2 "Building a decreases clause over (%s) and %s\n"
                (show bs) (show c);

          //exclude types and function-typed arguments from the decreases clause
          //and reveal and erased arguments
          let filter_types_and_functions (bs:binders)  =
            let out_rev, env = 
              List.fold_left 
                (fun (out, env) binder ->
                  let b = binder.binder_bv in
                  let t = N.unfold_whnf env (U.unrefine b.sort) in
                  let skip = is_precondition_binder env binder in
                  let env = Env.push_binders env [binder] in
                  match t.n with
                  | _ when skip ->
                    (out, env)
                  | Tm_type _
                  | Tm_arrow _ -> 
                    (out, env)
                  | _ ->
                    let arg = S.bv_to_name b in
                    let arg =
                      match is_erased_head t with
                      | Some (u, ty) -> U.apply_reveal u ty arg
                      | _ -> arg
                    in
                    (arg::out, env))
                ([], env)
                bs
            in
            List.rev out_rev
          in
          (* The [decreases] flag sits on the *innermost* comp.  A source
             precondition is now a trailing implicit binder, so the comp we are
             handed may still be a total arrow over those binders; look through
             them for the flag. *)
          let rec spec_flags env (c:comp) : ML (list cflag) =
            let fl = U.comp_flags c in
            if fl |> List.existsML (function DECREASES _ -> true | _ -> false)
            || not (U.is_total_comp c)
            then fl
            else match (SS.compress (U.comp_result c)).n with
                 | Tm_arrow {b=b'; comp=c'} when is_precondition_binder env b' ->
                   let bs', c' = SS.open_comp [b'] c' in
                   spec_flags (Env.push_binders env bs') c'
                 | _ -> fl in
          let cflags = spec_flags (Env.push_binders env bs) c in
          match cflags |> List.tryFind (function DECREASES _ -> true | _ -> false) with
                | Some (DECREASES d) -> d
                | _ -> bs |> filter_types_and_functions |> Decreases_lex
      in

      let precedes_t = S.fvar (Ident.set_lid_range Const.precedes_lid (Env.get_range env)) None in
      (* With [inst_univs], the universe-polymorphic [precedes] and [eq3] are
         instantiated with fresh universe variables, for the caller to solve
         when checking the refined types; otherwise, they are left for the
         elaborator to instantiate. *)
      let inst (lid:Ident.lident) (hd:term) : ML term =
        if inst_univs
        then let (us, _), _ = Env.lookup_lid env lid in
             S.mk_Tm_uinst hd (List.map (fun _ -> Env.new_u_univ ()) us)
        else hd in
      let mk_precedes_app (t_x t_x_prev x x_prev:term) : ML term =
        mk_Tm_app (inst Const.precedes_lid precedes_t) [iarg t_x; iarg t_x_prev; as_arg x; as_arg x_prev] r in
      let mk_eq3 (t1 t2 e1 e2:term) : ML term =
        mk_Tm_app (inst Const.eq3_lid (S.fvar Const.eq3_lid None)) [iarg t1; iarg t2; as_arg e1; as_arg e2]
          (Range.union_ranges e1.pos e2.pos) in
      let rec mk_precedes_lex env l l_prev : ML term =
        (*
         * AR: aux assumes that l and l_prev have the same lengths
         *     Given l = [a; b; c], l_prev = [d; e; f], it builds:
         *       a << d \/ (eq3 a d /\ b << e) \/ (eq3 a d /\ eq3 b e /\ c << f
         *     We build an "untyped" term here, the caller will typecheck it properly
         *)
        let rec aux l l_prev : ML term =
         let type_of (should_warn:bool) (e1:term) (e2:term) : ML (typ & typ) =
           (*
            * AR: we compute the types of e1 and e2 to provide type
            *     arguments to eq3 (otherwise F* may infer something that Z3 is unable
            *       to prove equal later on)
            *     as a check, if the types are not equal, we emit a warning so that
            *       the programmer may annotate explicitly if needed
            *)
           //AR: 03/30: WARNING: dropping the guard in computing t1 and t2 below
           let t1 = env.typeof_well_typed_tot_or_gtot_term env e1 false |> fst |> U.unrefine in
           let t2 = env.typeof_well_typed_tot_or_gtot_term env e2 false |> fst |> U.unrefine in
           let rec warn t1 t2 : ML _ =
             if TEQ.eq_tm env t1 t2 = TEQ.Equal
             then false
             else match (SS.compress t1).n, (SS.compress t2).n with
                  | Tm_uinst (t1, _), Tm_uinst (t2, _) -> warn t1 t2
                  | Tm_name _, Tm_name _ -> false  //do not warn for names, e.g. in polymorphic functions, the names may be instantiated at the call sites
                  | Tm_app _, Tm_app _ ->
                    let h1, args1 = U.head_and_args_full t1 in
                    let h2, args2 = U.head_and_args_full t2 in
                    warn h1 h2 || List.length args1 <> List.length args2 ||
                    (List.zip args1 args2 |> List.existsML (fun ((a1, _), (a2, _)) -> warn a1 a2))
                  | Tm_refine {b=t1; phi=phi1}, Tm_refine {b=t2; phi=phi2} ->
                    warn t1.sort t2.sort || warn phi1 phi2
                  | Tm_uvar _, _
                  | _, Tm_uvar _ -> false
                  | _, _ -> true in

           (* Not when elaborating: Core builds the termination goals with
              [guard_letrecs] again, when checking the elaborated term. *)
           (if not env.admit && should_warn && warn t1 t2
            then match (SS.compress t1).n, (SS.compress t2).n with
                 | Tm_name _, Tm_name _ -> ()
                 | _, _ ->
                   let open FStarC.Pprint in
                   let open FStarC.Class.PP in
                   Errors.log_issue e1 Errors.Warning_Defensive [
                     prefix 2 1 (text "In the decreases clause for this function, the SMT solver may not be able to prove that the types of")
                       (group (pp e1 ^/^ parens (text "bound in" ^/^ pp e1.pos))) ^/^
                     prefix 2 1 (text "and")
                       (group (pp e2 ^/^ parens (text "bound in" ^/^ pp e2.pos))) ^/^
                     text "are equal.";
                     prefix 2 1 (text "The type of the first term is:")  (pp t1);
                     prefix 2 1 (text "The type of the second term is:") (pp t2);
                     text "If the proof fails, try annotating these with the same type.";
                   ]);
           t1, t2 in

          match l, l_prev with
          | [], [] ->
            if inst_univs
            then mk_precedes_app S.t_unit S.t_unit S.unit_const S.unit_const
            else mk_Tm_app precedes_t [as_arg S.unit_const; as_arg S.unit_const] r
          | [x], [x_prev] -> 
            let t_x, t_x_prev = type_of false x x_prev in            
            mk_precedes_app t_x t_x_prev x x_prev
          | x::tl, x_prev::tl_prev ->
            let t_x, t_x_prev = type_of true x x_prev in
            let tm_precedes = mk_precedes_app t_x t_x_prev x x_prev in
            let eq3_x_x_prev = mk_eq3 t_x t_x_prev x x_prev in

            mk_disj tm_precedes
                    (mk_conj eq3_x_x_prev (aux tl tl_prev)) in

        (* Call aux with equal sized prefixes of l and l_prev *)
        let l, l_prev =
          let n, n_prev = List.length l, List.length l_prev in
          if n = n_prev then l, l_prev
          else if n < n_prev then l, l_prev |> List.splitAt n |> fst
          else l |> List.splitAt n_prev |> fst, l_prev in
        aux l l_prev in

      let mk_precedes (env:Env.env) d d_prev =
        match d, d_prev with
        | Decreases_lex l, Decreases_lex l_prev ->
          mk_precedes_lex env l l_prev
        | Decreases_wf (rel, e), Decreases_wf (rel_prev, e_prev) -> 
          (*
           * For well-founded relations based termination checking,
           *   just prove that (rel e e_prev)
           *)
          let rel_guard = mk_Tm_app rel [as_arg e; as_arg e_prev] r in
          if TEQ.eq_tm env rel rel_prev = TEQ.Equal
          then rel_guard
          else (
            (* if the relation is dependent on parameters in scope, 
               additionally prove that those parameters are invariant, 
               i.e., the rel and rel_prev are provably equal *)
               let t_rel, _ = 
                 Errors.with_ctx
                   ("Typechecking decreases well-founded relation")
                   (fun _ -> env.typeof_well_typed_tot_or_gtot_term env rel false)
               in
               let t_rel_prev, _ =
                 Errors.with_ctx
                   ("Typechecking previous decreases well-founded relation")                 
                   (fun _ -> env.typeof_well_typed_tot_or_gtot_term env rel_prev false)
               in
               let eq_guard = mk_eq3 t_rel t_rel_prev rel rel_prev in
               U.mk_conj eq_guard rel_guard
          )

        | _, _ ->
          Errors.raise_error r Errors.Fatal_UnexpectedTerm
            "Cannot build termination VC with a well-founded relation and lex ordering"
      in

      let previous_dec = decreases_clause actuals expected_c in

      let guard_one_letrec (l, arity, t, u_names) =
        let formals, c = N.get_n_binders_no_unrefine env arity t in

        (* This should never happen since `termination_check_enabled`
         * takes care to not return an arity bigger than the one in
         * the lbtyp. *)
        if arity > List.length formals then
          failwith "impossible: bad formals arity, guard_one_letrec";

        //make sure they all have non-null names
        let formals = formals |> List.map (fun b ->
          if S.is_null_bv b.binder_bv
          then ({b with binder_bv=S.new_bv (Some (S.range_of_bv b.binder_bv)) b.binder_bv.sort})
          else b) in
        let dec = decreases_clause formals c in
        let precedes =
          let env = Env.push_binders env formals in
          mk_precedes env dec previous_dec in
        let precedes = VCUtil.label (Errors.mkmsg "Could not prove termination of this recursive call") r precedes in
        (* The termination refinement must go on the last binder the caller
           actually supplies, so skip any trailing precondition binders. *)
        let env_formals = Env.push_binders env formals in
        let rec split_trailing_pre (bs:binders) : ML (binders & binders) =
          match bs with
          | [] -> [], []
          | b::tl ->
            match split_trailing_pre tl with
            | [], pre when is_precondition_binder env_formals b -> [], b::pre
            | real, pre -> b::real, pre
        in
        let real_formals, pre_formals = split_trailing_pre formals in
        let refined_formals =
          match real_formals with
          | [] -> (* nothing but preconditions; refine the last binder anyway *)
            let bs, ({binder_bv=last; binder_positivity=pqual; binder_attrs=attrs; binder_qual=imp}) = BU.prefix formals in
            let last = {last with sort=U.refine last precedes} in
            bs@[S.mk_binder_with_attrs last imp pqual attrs]
          | _ ->
            let bs, ({binder_bv=last; binder_positivity=pqual; binder_attrs=attrs; binder_qual=imp}) = BU.prefix real_formals in
            let last = {last with sort=U.refine last precedes} in
            bs@[S.mk_binder_with_attrs last imp pqual attrs]@pre_formals
        in
        let t' = U.arrow refined_formals c in
        if Debug.medium ()
        then Format.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
              (show l) (show t) (show t');
        l, t', u_names
      in
      letrecs |> List.map guard_one_letrec
