(*
   Copyright 2008-2016 Microsoft Research

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

module FStarC.Tactics.Hooks

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Util
open FStarC.Range
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.Tactics.Types
open FStarC.Tactics.Interpreter
open FStarC.Class.Show

module BU      = FStarC.Util
module Range   = FStarC.Range
module Err     = FStarC.Errors
module O       = FStarC.Options
module PC      = FStarC.Parser.Const
module S       = FStarC.Syntax.Syntax
module SS      = FStarC.Syntax.Subst
module U       = FStarC.Syntax.Util
module Print   = FStarC.Syntax.Print
module N       = FStarC.TypeChecker.Normalize
module Env     = FStarC.TypeChecker.Env
module TcUtil  = FStarC.TypeChecker.Util
module TcRel   = FStarC.TypeChecker.Rel
module TcTerm  = FStarC.TypeChecker.TcTerm
module TEQ     = FStarC.TypeChecker.TermEqAndSimplify

(* We only use the _abstract_ embeddings from this module,
hence there is no v1/v2 distinction. *)
module RE      = FStarC.Reflection.V2.Embeddings

let dbg_Tac        = Debug.get_toggle "Tac"
let dbg_SpinoffAll = Debug.get_toggle "SpinoffAll"

let run_tactic_on_typ
        (rng_tac : Range.range) (rng_goal : Range.range)
        (tactic:term) (env:Env.env) (typ:term)
                    : list goal // remaining goals
                    & term // witness
                    =
    let rng = range_of_rng (use_range rng_tac) (use_range rng_goal) in
    let ps, w = FStarC.Tactics.V2.Basic.proofstate_of_goal_ty rng env typ in
    let tactic_already_typed = false in
    let gs, _res = run_tactic_on_ps rng_tac rng_goal false e_unit () e_unit tactic tactic_already_typed ps in
    gs, w

let run_tactic_on_all_implicits
        (rng_tac : Range.range) (rng_goal : Range.range)
        (tactic:term) (env:Env.env) (imps:Env.implicits)
    : list goal // remaining goals
    =
    let ps, _ = FStarC.Tactics.V2.Basic.proofstate_of_all_implicits rng_goal env imps in
    let tactic_already_typed = false in
    let goals, () =
      run_tactic_on_ps
        (Env.get_range env)
        rng_goal
        true
        e_unit
        ()
        e_unit
        tactic
        tactic_already_typed
        ps
    in
    goals

// Polarity
type pol =
    | StrictlyPositive
    | Pos
    | Neg
    | Both // traversing both polarities at once

// Result of traversal
type tres_m 'a =
    | Unchanged of 'a
    | Simplified of 'a & list goal
    | Dual of 'a & 'a & list goal

type tres = tres_m term

let tpure x = Unchanged x

let flip p = match p with
    | StrictlyPositive -> Neg
    | Pos -> Neg
    | Neg -> Pos
    | Both -> Both

let getprop (e:Env.env) (t:term) : option term =
    let tn = N.normalize [Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant] e t in
    U.un_squash tn

let by_tactic_interp (pol:pol) (e:Env.env) (t:term) : tres =
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with

    // with_tactic marker
    | Tm_fvar fv, [(tactic, None); (assertion, None)]
            when S.fv_eq_lid fv PC.by_tactic_lid ->
        begin match pol with
        | StrictlyPositive
        | Pos ->
            let gs, _ = run_tactic_on_typ tactic.pos assertion.pos tactic e assertion in
            Simplified (FStarC.Syntax.Util.t_true, gs)

        | Both ->
            let gs, _ = run_tactic_on_typ tactic.pos assertion.pos tactic e assertion in
            Dual (assertion, FStarC.Syntax.Util.t_true, gs)

        | Neg ->
            // Peel away tactics in negative positions, they're assumptions!
            Simplified (assertion, [])
        end

    // spinoff marker: simply spin off a query independently.
    // So, equivalent to `with_tactic idtac` without importing the (somewhat heavy) tactics module
    | Tm_fvar fv, [(assertion, None)]
            when S.fv_eq_lid fv PC.spinoff_lid ->
        begin  match pol with
        | StrictlyPositive
        | Pos ->
          let g = fst <| goal_of_goal_ty e assertion in
          let g = set_label "spun-off assertion" g in
          Simplified (FStarC.Syntax.Util.t_true, [g])

        | Both ->
          let g = fst <| goal_of_goal_ty e assertion in
          let g = set_label "spun-off assertion" g in
          Dual (assertion, FStarC.Syntax.Util.t_true, [g])

        | Neg ->
          Simplified (assertion, [])
        end

    // rewrite_with_tactic marker
    | Tm_fvar fv, [(tactic, None); (typ, Some ({ aqual_implicit = true } )); (tm, None)]
            when S.fv_eq_lid fv PC.rewrite_by_tactic_lid ->

        // Create a new uvar that must be equal to the initial term
        let uvtm, _, g_imp = Env.new_implicit_var_aux "rewrite_with_tactic RHS" tm.pos e typ Strict None false in

        let u = e.universe_of e typ in
        // eq2 is squashed already, so it's in Type0
        let goal = U.mk_squash U_zero (U.mk_eq2 u typ tm uvtm) in
        let gs, _ = run_tactic_on_typ tactic.pos tm.pos tactic e goal in

        // abort if the uvar was not solved
        let tagged_imps = TcRel.resolve_implicits_tac e g_imp in
        report_implicits tm.pos tagged_imps;

        // If the rewriting succeeded, we return the generated uvar, which is now
        // a synthesized term. Any unsolved goals (gs) are spun off.
        Simplified (uvtm, gs)

    | _ ->
        Unchanged t

let explode (t : tres_m 'a) : 'a & 'a & list goal =
    match t with
    | Unchanged t -> (t, t, [])
    | Simplified (t, gs) -> (t, t, gs)
    | Dual (tn, tp, gs) -> (tn, tp, gs)

let comb1 (f : 'a -> 'b) : tres_m 'a -> tres_m 'b = function
    | Unchanged t -> Unchanged (f t)
    | Simplified (t, gs) -> Simplified (f t, gs)
    | Dual (tn, tp, gs) -> Dual (f tn, f tp, gs)

let comb2 (f : 'a -> 'b -> 'c ) (x : tres_m 'a) (y : tres_m 'b) : tres_m 'c =
    match x, y with
    | Unchanged t1, Unchanged t2 ->
        Unchanged (f t1 t2)

    | Unchanged t1, Simplified (t2, gs)
    | Simplified (t1, gs), Unchanged t2 ->
        Simplified (f t1 t2, gs)

    | Simplified (t1, gs1), Simplified (t2, gs2) ->
        Simplified (f t1 t2, gs1@gs2)

    | _ ->
        let (n1, p1, gs1) = explode x in
        let (n2, p2, gs2) = explode y in
        Dual (f n1 n2, f p1 p2, gs1@gs2)

let comb_list (rs : list (tres_m 'a)) : tres_m (list 'a) =
    let rec aux rs acc =
        match rs with
        | [] -> acc
        | hd::tl -> aux tl (comb2 (fun l r -> l::r) hd acc)
    in
    aux (List.rev rs) (tpure [])

let emit (gs : list goal) (m : tres_m 'a) : tres_m 'a =
    comb2 (fun () x -> x) (Simplified ((), gs)) m

let rec traverse (f: pol -> Env.env -> term -> tres) (pol:pol) (e:Env.env) (t:term) : tres =
    let r =
        match (SS.compress t).n with
        | Tm_uinst (t,us) -> let tr = traverse f pol e t in
                             comb1 (fun t' -> Tm_uinst (t', us)) tr

        | Tm_meta {tm=t; meta=m} -> let tr = traverse f pol e t in
                            comb1 (fun t' -> Tm_meta {tm=t'; meta=m}) tr

        | Tm_app {hd={ n = Tm_fvar fv }; args=[(p,_); (q,_)]} when S.fv_eq_lid fv PC.imp_lid ->
               // ==> is specialized to U_zero
               let x = S.new_bv None p in
               let r1 = traverse f (flip pol)  e                p in
               let r2 = traverse f       pol  (Env.push_bv e x) q in
               comb2 (fun l r -> (U.mk_imp l r).n) r1 r2

        (* p <==> q is special, each side is bipolar *)
        (* So we traverse its arguments with pol = Both, and negative and positive versions *)
        (* of p and q *)
        (* then we return (in general) (p- ==> q+) /\ (q- ==> p+) *)
        (* But if neither side ran tactics, we just keep p <==> q *)
        | Tm_app {hd={ n = Tm_fvar fv }; args=[(p,_); (q,_)]} when S.fv_eq_lid fv PC.iff_lid ->
               // <==> is specialized to U_zero
               let xp = S.new_bv None p in
               let xq = S.new_bv None q in
               let r1 = traverse f Both (Env.push_bv e xq) p in
               let r2 = traverse f Both (Env.push_bv e xp) q in
               // Should be flipping the tres, I think
               begin match r1, r2 with
               | Unchanged _, Unchanged _ ->
                  comb2 (fun l r -> (U.mk_iff l r).n) r1 r2
               | _ ->
                  let (pn, pp, gs1) = explode r1 in
                  let (qn, qp, gs2) = explode r2 in
                  let t = U.mk_conj (U.mk_imp pn qp) (U.mk_imp qn pp) in
                  Simplified (t.n, gs1@gs2)
               end

        | Tm_app {hd; args} ->
                let r0 = traverse f pol e hd in
                let r1 = List.fold_right (fun (a, q) r ->
                                              let r' = traverse f pol e a in
                                              comb2 (fun a args -> (a, q)::args) r' r)
                                                 args (tpure []) in
                comb2 (fun hd args -> Tm_app {hd; args}) r0 r1

        | Tm_abs {bs; body=t; rc_opt=k} ->
                // TODO: traverse k?
                let bs, topen = SS.open_term bs t in
                let e' = Env.push_binders e bs in
                let r0 = List.map (fun b ->
                                     let r = traverse f (flip pol) e b.binder_bv.sort in
                                     comb1 (fun s' -> ({b with binder_bv={ b.binder_bv with sort = s' }})) r
                                  ) bs
                in
                let rbs = comb_list r0 in
                let rt = traverse f pol e' topen in
                comb2 (fun bs t -> (U.abs bs t k).n) rbs rt

        | Tm_ascribed {tm=t;asc;eff_opt=ef} ->
            // TODO: traverse the types?
            comb1 (fun t -> Tm_ascribed {tm=t; asc; eff_opt=ef}) (traverse f pol e t)

        | Tm_match {scrutinee=sc; ret_opt=asc_opt; brs; rc_opt=lopt} ->  //AR: not traversing the return annotation
            comb2 (fun sc brs -> Tm_match {scrutinee=sc; ret_opt=asc_opt; brs; rc_opt=lopt})
                  (traverse f pol e sc)
                  (comb_list (List.map (fun br -> let (pat, w, exp) = SS.open_branch br in
                                                  let bvs = S.pat_bvs pat in
                                                  let e = Env.push_bvs e bvs in
                                                  let r = traverse f pol e exp in
                                                  comb1 (fun exp -> SS.close_branch (pat, w, exp)) r) brs))

        | x ->
            tpure x in
    match r with
    | Unchanged tn' ->
        f pol e ({ t with n = tn' })

    | Simplified (tn', gs) ->
        emit gs (f pol e ({ t with n = tn' }))

    | Dual (tn, tp, gs) ->
        let rp = f pol e ({ t with n = tp }) in
        let (_, p', gs') = explode rp in
        Dual ({t with n = tn}, p', gs@gs')

let preprocess (env:Env.env) (goal:term)
  : bool & list (Env.env & term & O.optionstate)
    (* bool=true iff any tactic actually ran *)
=
  Errors.with_ctx "While preprocessing VC with a tactic" (fun () ->
    if !dbg_Tac then
        BU.print2 "About to preprocess %s |= %s\n"
                        (show <| Env.all_binders env)
                        (show goal);
    let initial = (1, []) in
    // This match should never fail
    let did_anything, (t', gs) =
        match traverse by_tactic_interp Pos env goal with
        | Unchanged t' -> false, (t', [])
        | Simplified (t', gs) -> true, (t', gs)
        | _ -> failwith "preprocess: impossible, traverse returned a Dual"
    in
    if !dbg_Tac then
        BU.print2 "Main goal simplified to: %s |- %s\n"
                (show <| Env.all_binders env)
                (show t');
    let s = initial in
    let s = List.fold_left (fun (n,gs) g ->
                 let phi = match getprop (goal_env g) (goal_type g) with
                           | None ->
                                Err.raise_error env Err.Fatal_TacticProofRelevantGoal
                                  (BU.format1 "Tactic returned proof-relevant goal: %s" (show (goal_type g)))
                           | Some phi -> phi
                 in
                 if !dbg_Tac then
                     BU.print2 "Got goal #%s: %s\n" (show n) (show (goal_type g));
                 let label =
                   let open FStarC.Pprint in
                   let open FStarC.Class.PP in
                   [
                    doc_of_string "Could not prove goal #" ^^ pp n ^/^
                    (if get_label g = "" then empty else parens (doc_of_string <| get_label g))
                   ]
                 in
                 let gt' = TcUtil.label label (goal_range g) phi in
                 (n+1, (goal_env g, gt', goal_opts g)::gs)) s gs in
    let (_, gs) = s in
    let gs = List.rev gs in (* Return new VCs in same order as goals *)
    // Use default opts for main goal
    did_anything, (env, t', O.peek ()) :: gs
  )

let rec traverse_for_spinoff
                 (pol:pol)
                 (label_ctx:option (list Pprint.document & Range.range))
                 (e:Env.env)
                 (t:term) : tres =
    let debug_any = Debug.any () in
    let traverse pol e t = traverse_for_spinoff pol label_ctx e t in
    let traverse_ctx pol (ctx : list Pprint.document & Range.range) (e:Env.env) (t:term) : tres =
      let print_lc (msg, rng) =
        BU.format3 "(%s,%s) : %s"
          (Range.string_of_def_range rng)
          (Range.string_of_use_range rng)
          (Errors.Msg.rendermsg msg)
      in
       if !dbg_SpinoffAll
       then BU.print2 "Changing label context from %s to %s"
             (match label_ctx with
              | None -> "None"
              | Some lc -> print_lc lc)
             (print_lc ctx);
       traverse_for_spinoff pol (Some ctx) e t
    in
    let should_descend (t:term) =
        //descend only into the following connectives
        let hd, args = U.head_and_args t in
        let res =
          match (U.un_uinst hd).n with
          | Tm_fvar fv ->
            S.fv_eq_lid fv PC.and_lid ||
            S.fv_eq_lid fv PC.imp_lid ||
            S.fv_eq_lid fv PC.forall_lid ||
            S.fv_eq_lid fv PC.auto_squash_lid ||
            S.fv_eq_lid fv PC.squash_lid

          | Tm_meta _
          | Tm_ascribed _
          | Tm_abs _ ->
            true

          | _ ->
            false
          in
          res
    in
    let maybe_spinoff pol
                      (label_ctx:option (list Pprint.document & Range.range))
                      (e:Env.env)
                      (t:term)
      : tres =
        let label_goal (env, t) =
            let t =
              match (SS.compress t).n, label_ctx with
              | Tm_meta {meta=Meta_labeled _}, _ -> t
              | _, Some (msg, r) -> TcUtil.label msg r t
              | _ -> t
            in
            let t =
              if U.is_sub_singleton t
              then t
              else U.mk_auto_squash U_zero t
            in
            fst (goal_of_goal_ty env t)
        in
        let spinoff t =
          match pol with
          | StrictlyPositive ->
            if !dbg_SpinoffAll then BU.print1 "Spinning off %s\n" (show t);
            Simplified (FStarC.Syntax.Util.t_true, [label_goal (e,t)])

          | _ ->
            Unchanged t
        in
        let t = SS.compress t in
        if not (should_descend t)
        then spinoff t
        else Unchanged t
    in
    let rewrite_boolean_conjunction t =
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(t, _)]
                    when S.fv_eq_lid fv PC.b2t_lid -> (
            let hd, args = U.head_and_args t in
            match (U.un_uinst hd).n, args with
            | Tm_fvar fv, [(t0, _); (t1, _)]
              when S.fv_eq_lid fv PC.op_And ->
              let t = U.mk_conj (U.b2t t0) (U.b2t t1) in
              Some t
            | _ ->
              None
            )
        | _ -> None
    in
    let try_rewrite_match env t =
        let rec pat_as_exp env p =
          match FStarC.TypeChecker.PatternUtils.raw_pat_as_exp env p with
          | None -> None
          | Some (e, _) ->
            let env, _ = Env.clear_expected_typ env in
            let e, lc =
              FStarC.TypeChecker.TcTerm.tc_trivial_guard ({env with FStarC.TypeChecker.Env.admit=true}) e in
            let u = 
              FStarC.TypeChecker.TcTerm.universe_of env lc.res_typ in
            Some (e, lc.res_typ, u)
        in
        let bv_universes env bvs =
          List.map (fun x -> x, FStarC.TypeChecker.TcTerm.universe_of env x.sort) bvs
        in
        let mk_forall_l bv_univs term = 
          List.fold_right
            (fun (x,u) out -> U.mk_forall u x out)
            bv_univs
            term
        in
        let mk_exists_l bv_univs term = 
          List.fold_right
            (fun (x,u) out -> U.mk_exists u x out)
            bv_univs
            term
        in        
        if pol <> StrictlyPositive then None
        else (
          match (SS.compress t).n with
          | Tm_match {scrutinee=sc; ret_opt=asc_opt; brs; rc_opt=lopt} ->  //AR: not traversing the return annotation
            let rec rewrite_branches path_condition branches =
              match branches with
              | [] -> Inr (U.mk_imp path_condition U.t_false)
              | br::branches ->
                let pat, w, body = SS.open_branch br in
                match w with
                | Some _ -> 
                  Inl "when clause" //don't handle when clauses
                | _ -> 
                  let bvs = S.pat_bvs pat in
                  let env = Env.push_bvs env bvs in
                  let bvs_univs = bv_universes env bvs in
                  match pat_as_exp env pat with
                  | None -> Inl "Ill-typed pattern"
                  | Some (p_e, t, u) ->
                    let eqn = U.mk_eq2 u t sc p_e in
                    let branch_goal = mk_forall_l bvs_univs (U.mk_imp eqn body) in
                    let branch_goal = U.mk_imp path_condition branch_goal in
                    let next_path_condition = U.mk_conj path_condition (U.mk_neg (mk_exists_l bvs_univs eqn)) in
                    match rewrite_branches next_path_condition branches with
                    | Inl msg -> Inl msg
                    | Inr rest -> Inr (U.mk_conj branch_goal rest)
            in
            let res = rewrite_branches U.t_true brs in
            (match res with
             | Inl msg ->
               if debug_any
               then FStarC.Errors.diag 
                      (Env.get_range env)
                      (BU.format2 "Failed to split match term because %s (%s)" msg (show t));
               None
             | Inr res ->
               if debug_any
               then FStarC.Errors.diag 
                      (Env.get_range env)
                      (BU.format2 "Rewrote match term\n%s\ninto %s\n"
                        (show t)
                        (show res));
             
               Some res)
          | _ -> None
        )
    in
    let maybe_rewrite_term t =
      if pol <> StrictlyPositive then None
      else
        match rewrite_boolean_conjunction t with
        | Some t -> Some t
        | None -> try_rewrite_match e t 
    in
    match maybe_rewrite_term t with
    | Some t ->
      traverse pol e t
    | _ ->
      let r =
        let t = SS.compress t in
        if not (should_descend t) then tpure t.n
        else begin
          match t.n with
          | Tm_uinst (t,us) ->
            let tr = traverse pol e t in
            comb1 (fun t' -> Tm_uinst (t', us)) tr

          | Tm_meta {tm=t; meta=Meta_labeled(msg, r, _)} ->
            let tr = traverse_ctx pol (msg, r) e t in
            comb1 (fun t' -> Tm_meta {tm=t'; meta=Meta_labeled(msg, r, false)}) tr

          | Tm_meta {tm=t; meta=m} ->
            let tr = traverse pol e t in
            comb1 (fun t' -> Tm_meta {tm=t'; meta=m}) tr

          | Tm_ascribed {tm=t; asc; eff_opt=ef} ->
            // TODO: traverse the types?
            comb1 (fun t -> Tm_ascribed {tm=t; asc; eff_opt=ef}) (traverse pol e t)

          | Tm_app {hd={ n = Tm_fvar fv }; args=[(p,_); (q,_)]} when S.fv_eq_lid fv PC.imp_lid ->
                 // ==> is specialized to U_zero
            let x = S.new_bv None p in
            let r1 = traverse (flip pol)  e                p in
            let r2 = traverse       pol  (Env.push_bv e x) q in
            comb2 (fun l r -> (U.mk_imp l r).n) r1 r2

          | Tm_app {hd; args} ->
            begin
            match (U.un_uinst hd).n, args with
            | Tm_fvar fv, [(t, Some aq0); (body, aq)]
               when (S.fv_eq_lid fv PC.forall_lid ||
                     S.fv_eq_lid fv PC.exists_lid) &&
                    aq0.aqual_implicit ->
                let r0 = traverse pol e hd in
                let rt = traverse (flip pol) e t in
                let rbody = traverse pol e body in
                let rargs = comb2 (fun t body -> [(t, Some aq0); (body, aq)]) rt rbody in
                comb2 (fun hd args -> Tm_app {hd; args}) r0 rargs

            | _ ->
                let r0 = traverse pol e hd in
                let r1 =
                  List.fold_right
                    (fun (a, q) r ->
                       let r' = traverse pol e a in
                       comb2 (fun a args -> (a, q)::args) r' r)
                    args
                    (tpure [])
                in
                let simplified = Simplified? r0 || Simplified? r1 in
                comb2
                    (fun hd args ->
                       match (U.un_uinst hd).n, args with
                       | Tm_fvar fv, [(t, _)]
                         when simplified &&
                              S.fv_eq_lid fv PC.squash_lid &&
                              TEQ.eq_tm e t U.t_true = TEQ.Equal ->
                         //simplify squash True to True
                         //important for simplifying queries to Trivial
                         if !dbg_SpinoffAll then BU.print_string "Simplified squash True to True";
                         U.t_true.n

                       | _ ->
                         let t' = Tm_app {hd; args} in
                         t')
                    r0 r1                  
            end

          | Tm_abs {bs; body=t; rc_opt=k} ->
                // TODO: traverse k?
                let bs, topen = SS.open_term bs t in
                let e' = Env.push_binders e bs in
                let r0 = List.map (fun b ->
                                     let r = traverse (flip pol) e b.binder_bv.sort in
                                     comb1 (fun s' -> ({b with binder_bv={ b.binder_bv with sort = s' }})) r
                                  ) bs
                in
                let rbs = comb_list r0 in
                let rt = traverse pol e' topen in
                comb2 (fun bs t -> (U.abs bs t k).n) rbs rt

          | x ->
            tpure x
        end
    in
    match r with
    | Unchanged tn' ->
        maybe_spinoff pol label_ctx e ({ t with n = tn' })

    | Simplified (tn', gs) ->
        emit gs (maybe_spinoff pol label_ctx e ({ t with n = tn' }))

    | Dual (tn, tp, gs) ->
        let rp = maybe_spinoff pol label_ctx e ({ t with n = tp }) in
        let (_, p', gs') = explode rp in
        Dual ({t with n = tn}, p', gs@gs')

let pol_to_string = function
  | StrictlyPositive -> "StrictlyPositive"
  | Pos -> "Positive"
  | Neg -> "Negative"
  | Both -> "Both"

let spinoff_strictly_positive_goals (env:Env.env) (goal:term)
  : list (Env.env & term)
  = if !dbg_SpinoffAll then BU.print1 "spinoff_all called with %s\n" (show goal);
    Errors.with_ctx "While spinning off all goals" (fun () ->
      let initial = (1, []) in
      // This match should never fail
      let (t', gs) =
          match traverse_for_spinoff StrictlyPositive None env goal with
          | Unchanged t' -> (t', [])
          | Simplified (t', gs) -> (t', gs)
          | _ -> failwith "preprocess: impossible, traverse returned a Dual"
      in
      let t' =
          N.normalize [Env.Eager_unfolding; Env.Simplify; Env.Primops] env t'
      in
      let main_goal =
        let t = FStarC.TypeChecker.Common.check_trivial t' in
        match t with
        | Trivial -> []
        | NonTrivial t ->
          if !dbg_SpinoffAll
          then (
            let msg = BU.format2 "Main goal simplified to: %s |- %s\n"
                            (show <| Env.all_binders env)
                            (show t) in
            FStarC.Errors.diag
              (Env.get_range env)
              (BU.format1 
               "Verification condition was to be split into several atomic sub-goals, \
                but this query had some sub-goals that couldn't be split---the error report, if any, may be \
                inaccurate.\n%s\n"
               msg)
          );
          [(env, t)]
      in
      let s = initial in
      let s =
        List.fold_left
          (fun (n,gs) g ->
             let phi = goal_type g in
             (n+1, (goal_env g, phi)::gs))
          s
          gs
      in
      let (_, gs) = s in
      let gs = List.rev gs in (* Return new VCs in same order as goals *)
      let gs =
        gs |>
        List.filter_map
          (fun (env, t) ->
            let t = N.normalize [Env.Eager_unfolding; Env.Simplify; Env.Primops] env t in
            match FStarC.TypeChecker.Common.check_trivial t with
            | Trivial -> None
            | NonTrivial t ->
              if !dbg_SpinoffAll
              then BU.print1 "Got goal: %s\n" (show t);
              Some (env, t))
      in

      FStarC.Errors.diag (Env.get_range env)
              (BU.format1 "Split query into %s sub-goals" (show (List.length gs)));

      main_goal@gs
  )


let synthesize (env:Env.env) (typ:typ) (tau:term) : term =
  Errors.with_ctx "While synthesizing term with a tactic" (fun () ->
    // Don't run the tactic (and end with a magic) when flychecking is set, cf. issue #73 in fstar-mode.el
    if env.flychecking
    then mk_Tm_app (TcUtil.fvar_env env PC.magic_lid) [S.as_arg U.exp_unit] typ.pos
    else begin

    let gs, w = run_tactic_on_typ tau.pos typ.pos tau env typ in
    // Check that all goals left are irrelevant and provable
    // TODO: It would be nicer to combine all of these into a guard and return
    // that to TcTerm, but the varying environments make it awkward.
    gs |> List.iter (fun g ->
        match getprop (goal_env g) (goal_type g) with
        | Some vc ->
            begin
            if !dbg_Tac then
              BU.print1 "Synthesis left a goal: %s\n" (show vc);
            let guard = guard_of_guard_formula (NonTrivial vc) in
            TcRel.force_trivial_guard (goal_env g) guard
            end
        | None ->
            Err.raise_error typ Err.Fatal_OpenGoalsInSynthesis "synthesis left open goals");
    w
    end
  )

let solve_implicits (env:Env.env) (tau:term) (imps:Env.implicits) : unit =
  Errors.with_ctx "While solving implicits with a tactic" (fun () ->
    if env.flychecking then () else
    begin

    let gs = run_tactic_on_all_implicits tau.pos (Env.get_range env) tau env imps in
    // Check that all goals left are irrelevant and provable
    // TODO: It would be nicer to combine all of these into a guard and return
    // that to TcTerm, but the varying environments make it awkward.
    if Options.profile_enabled None "FStarC.TypeChecker"
    then BU.print1 "solve_implicits produced %s goals\n" (show (List.length gs));
    
    Options.with_saved_options (fun () ->
      let _ = Options.set_options "--no_tactics" in
      gs |> List.iter (fun g ->
        Options.set (goal_opts g);
        match getprop (goal_env g) (goal_type g) with
        | Some vc ->
          begin
            if !dbg_Tac then
              BU.print1 "Synthesis left a goal: %s\n" (show vc);
            if not env.admit
            then (
              let guard = guard_of_guard_formula (NonTrivial vc) in
              Profiling.profile (fun () ->
                TcRel.force_trivial_guard (goal_env g) guard)
              None
              "FStarC.TypeChecker.Hooks.force_trivial_guard"
            )
          end
        | None ->
            Err.raise_error env Err.Fatal_OpenGoalsInSynthesis "synthesis left open goals"
      ))
    end
  )

(* Retrieves a tactic associated to a given attribute, if any *)
let find_user_tac_for_attr env (a:term) : option sigelt =
  let hooks = Env.lookup_attr env (Ident.string_of_lid PC.handle_smt_goals_attr) in
  hooks |> BU.try_find (fun _ -> true)

(* This function takes an environment [env] and a goal [goal], and tries to run
   the tactic registered with the (handle_smt_goal) attribute, if any.
   If such a tactic exists, all the unresolved goals must be propositions,
   that will be directly encoded to SMT inside Rel.discharge_guard.
   If such a tactic does not exist, this function is a no-op. *)
let handle_smt_goal env goal =
  match check_trivial goal with
  (* No need to pass the term to the tactic if trivial *)
  | Trivial -> [env, goal]
  | NonTrivial goal ->
    (* Attempt to retrieve a tactic corresponding to the (handle_smt_goals) attribute *)
    match find_user_tac_for_attr env (S.tconst PC.handle_smt_goals_attr) with
    | Some tac ->
      (* There is a tactic registered with the handle_smt_goals attribute,
         we retrieve the corresponding term  *)
      let tau =
        match tac.sigel with
        | Sig_let {lids=[lid]} ->
          let qn = Env.lookup_qname env lid in
          let fv = S.lid_as_fv lid None in
          S.fv_to_tm (S.lid_as_fv lid None)
        | _ -> failwith "Resolve_tac not found"
      in

     let gs = Errors.with_ctx "While handling an SMT goal with a tactic" (fun () ->

        (* Executing the tactic on the goal. *)
        let gs, _ = run_tactic_on_typ tau.pos (Env.get_range env) tau env (U.mk_squash U_zero goal) in
        // Check that all goals left are irrelevant and provable
        gs |> List.map (fun g ->
            match getprop (goal_env g) (goal_type g) with
            | Some vc ->
                if !dbg_Tac then
                  BU.print1 "handle_smt_goals left a goal: %s\n" (show vc);
                (goal_env g), vc
            | None ->
                Err.raise_error env Err.Fatal_OpenGoalsInSynthesis "Handling an SMT goal by tactic left non-prop open goals")
      ) in

      gs

    (* No such tactic was available in the current context *)
    | None -> [env, goal]

// TODO: this is somehow needed for tcresolve to infer the embeddings in run_tactic_on_ps below
instance _ = RE.e_term

type blob_t = option (string & term)
type dsl_typed_sigelt_t = bool & sigelt & blob_t
type dsl_tac_result_t =
  list dsl_typed_sigelt_t &
  dsl_typed_sigelt_t &
  list dsl_typed_sigelt_t

let splice
  (env:Env.env)
  (is_typed:bool)
  (lids:list Ident.lident)
  (tau:term)
  (rng:Range.range) : list sigelt =
  
  Errors.with_ctx "While running splice with a tactic" (fun () ->
    if env.flychecking then [] else begin

    let tau, _, g =
      if is_typed
      then TcTerm.tc_check_tot_or_gtot_term env tau U.t_dsl_tac_typ None
      else TcTerm.tc_tactic t_unit S.t_decls env tau
    in

    TcRel.force_trivial_guard env g;

    let ps = FStarC.Tactics.V2.Basic.proofstate_of_goals tau.pos env [] [] in
    let tactic_already_typed = true in
    let gs, sigelts =
      if is_typed then
      begin
        //
        // See if there is a val for the lid
        //
        if List.length lids > 1
        then Err.raise_error rng Errors.Error_BadSplice
               (BU.format1 "Typed splice: unexpected lids length (> 1) (%s)" (show lids))
        else begin
          let val_t : option typ =  // val type, if any, for the lid
            //
            // For spliced vals, their lids is set to []
            //   (see ToSyntax.fst:desugar_decl, splice case)
            //
            if List.length lids = 0
            then None
            else
              match Env.try_lookup_val_decl env (List.hd lids) with
              | None -> None
              | Some ((uvs, tval), _) ->
                //
                // No universe polymorphic typed splice yet
                //
                if List.length uvs <> 0
                then
                  Err.raise_error rng Errors.Error_BadSplice 
                    (BU.format1 "Typed splice: val declaration for %s is universe polymorphic in %s universes, expected 0"
                       (show (List.length uvs)))
                else Some tval in

          //
          // The arguments to run_tactic_on_ps here are in sync with ulib/FStarC.Tactics.dsl_tac_t
          //
          let (gs, (sig_blobs_before, sig_blob, sig_blobs_after))
            : list goal & dsl_tac_result_t =
            run_tactic_on_ps tau.pos tau.pos false
              FStar.Tactics.Typeclasses.solve
              ({env with gamma=[]}, val_t)
              FStar.Tactics.Typeclasses.solve
              tau
              tactic_already_typed
              ps
          in
          let sig_blobs = sig_blobs_before@(sig_blob::sig_blobs_after) in
          let sigelts = sig_blobs |> map (fun (checked, se, blob_opt) ->
            { se with
                sigmeta = { se.sigmeta with
                  sigmeta_extension_data =
                        (match blob_opt with
                         | Some (s, blob) -> [s, Dyn.mkdyn blob]
                         | None -> []);
                  sigmeta_already_checked = checked; }
            }
          )
          in
          gs, sigelts
        end
      end
      else run_tactic_on_ps tau.pos tau.pos false
             e_unit ()
             (e_list RE.e_sigelt) tau tactic_already_typed ps
    in

    // Set proper ranges in the sigelts. This is very important
    // for the interactive mode, so that jump to definition works.
    let sigelts =
      let proc_lb lb =
        let {lbname=Inr fv; lbdef} = lb in
        let r =
          (* If this name was provided in the definition list of the splice,
          prefer that range. Otherwise set range to the full splice. *)
          match tryFind (fun i -> Ident.lid_equals i fv.fv_name.v) lids with
          | Some i -> pos i
          | _ -> rng
        in
        let fv = setPos r fv in
        {lb with lbname=Inr fv}
      in
      List.map (fun se ->
        match se.sigel with
        | Sig_let {lbs=(is_rec, lbs); lids} ->
          {se with sigel=Sig_let {lbs=(is_rec, List.map proc_lb lbs); lids}}
        | _ -> se
      ) sigelts
    in

    // Check that all goals left are irrelevant and solve them.
    Options.with_saved_options (fun () ->
      List.iter (fun g ->
        Options.set (goal_opts g);
        match getprop (goal_env g) (goal_type g) with
        | Some vc ->
            begin
            if !dbg_Tac then
              BU.print1 "Splice left a goal: %s\n" (show vc);
            let guard = guard_of_guard_formula (NonTrivial vc) in
            TcRel.force_trivial_guard (goal_env g) guard
            end
        | None ->
            Err.raise_error rng Err.Fatal_OpenGoalsInSynthesis "splice left open goals") gs);

    let lids' = List.collect U.lids_of_sigelt sigelts in
    List.iter (fun lid ->
      match List.tryFind (Ident.lid_equals lid) lids' with
      (* If env.flychecking is on, nothing will be generated, so don't raise an error
       * so flycheck does spuriously not mark the line red *)
      | None when not env.flychecking ->
        Err.raise_error rng Errors.Fatal_SplicedUndef
          (BU.format2 "Splice declared the name %s but it was not defined.\nThose defined were: %s"
             (show lid) (show lids'))
      | _ -> ()
    ) lids;

    if !dbg_Tac then
      BU.print1 "splice: got decls = {\n\n%s\n\n}\n" (show sigelts);

    (* Check for bare Sig_datacon and Sig_inductive_typ, and abort if so. Also set range. *)
    let sigelts = sigelts |> List.map (fun se ->
        begin match se.sigel with
        | Sig_datacon _
        | Sig_inductive_typ _ ->
          let open FStarC.Pprint in
          let open FStarC.Errors.Msg in
          Err.raise_error rng Err.Error_BadSplice [
            text "Tactic returned bad sigelt:" ^/^ doc_of_string (Print.sigelt_to_string_short se);
            text "If you wanted to splice an inductive type, call `pack` providing a `Sg_Inductive` to get a proper sigelt."
          ]
        | _ -> ()
        end;
        { se with sigrng = rng })
    in

    (* Check there are no internal qualifiers *)
    let () =
      if is_typed then ()
      else
        sigelts |> List.iter (fun se ->
        se.sigquals |> List.iter (fun q ->
          (* NOTE: Assumption is OK, a tactic can generate an axiom, but
           * it will be reported with --report_assumes. *)
          if is_internal_qualifier q then
            let open FStarC.Errors.Msg in
            let open FStarC.Pprint in
            Err.raise_error rng Err.Error_InternalQualifier [
              text <| BU.format1 "The qualifier %s is internal." (show q);
              prefix 2 1 (text "It cannot be attached to spliced declaration:")
                (arbitrary_string (Print.sigelt_to_string_short se));
            ]
         ))
    in
    sigelts
    end
  )

let mpreprocess (env:Env.env) (tau:term) (tm:term) : term =
  Errors.with_ctx "While preprocessing a definition with a tactic" (fun () ->
    if env.flychecking then tm else begin
    let ps = FStarC.Tactics.V2.Basic.proofstate_of_goals tm.pos env [] [] in
    let tactic_already_typed = false in
    let gs, tm = run_tactic_on_ps tau.pos tm.pos false RE.e_term tm RE.e_term tau tactic_already_typed ps in
    tm
    end
  )

let postprocess (env:Env.env) (tau:term) (typ:term) (tm:term) : term =
  Errors.with_ctx "While postprocessing a definition with a tactic" (fun () ->
    if env.flychecking then tm else begin
    //we know that tm:typ
    //and we have a goal that u == tm
    //so if we solve that equality, we don't need to retype the solution of `u : typ`
    let uvtm, _, g_imp = Env.new_implicit_var_aux "postprocess RHS" tm.pos env typ (Allow_untyped "postprocess") None false in

    let u = env.universe_of env typ in
    // eq2 is squashed already, so it's in Type0
    let goal = U.mk_squash U_zero (U.mk_eq2 u typ tm uvtm) in
    let gs, w = run_tactic_on_typ tau.pos tm.pos tau env goal in
    // see comment in `synthesize`
    List.iter (fun g ->
        match getprop (goal_env g) (goal_type g) with
        | Some vc ->
            begin
            if !dbg_Tac then
              BU.print1 "Postprocessing left a goal: %s\n" (show vc);
            let guard = guard_of_guard_formula (NonTrivial vc) in
            TcRel.force_trivial_guard (goal_env g) guard
            end
        | None ->
            Err.raise_error typ Err.Fatal_OpenGoalsInSynthesis "postprocessing left open goals") gs;
    (* abort if the uvar was not solved *)
    let tagged_imps = TcRel.resolve_implicits_tac env g_imp in
    report_implicits tm.pos tagged_imps;

    uvtm
    end
  )
