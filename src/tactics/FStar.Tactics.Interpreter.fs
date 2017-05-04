#light "off"
module FStar.Tactics.Interpreter
open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Range

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module SC = FStar.Syntax.Const
module Env = FStar.TypeChecker.Env
module BU = FStar.Util
module U = FStar.Syntax.Util
module Rel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module N = FStar.TypeChecker.Normalize
open FStar.Tactics.Basic
module E = FStar.Tactics.Embedding
module Core = FStar.Tactics.Basic
open FStar.Reflection.Basic
open FStar.Reflection.Interpreter

let mk_tactic_interpretation_0 (ps:proofstate) (t:tac<'a>) (embed_a:'a -> term) (t_a:typ) (nm:Ident.lid) (args:args) : option<term> =
 (*  We have: t () embedded_state
     The idea is to:
        1. unembed the state
        2. run the `t` tactic
        3. embed the result and final state and return it to the normalizer
  *)
  match args with
  | [(embedded_state, _)] ->
    if !tacdbg then
    BU.print2 "Reached %s, args are: %s\n"
            (Ident.string_of_lid nm)
            (Print.args_to_string args);
    let goals, smt_goals = E.unembed_state ps.main_context embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run t ps in
    Some (E.embed_result res embed_a t_a)
  | _ ->
    failwith ("Unexpected application of tactic primitive")

let mk_tactic_interpretation_1 (ps:proofstate)
                               (t:'b -> tac<'a>) (unembed_b:term -> 'b)
                               (embed_a:'a -> term) (t_a:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(b, _); (embedded_state, _)] ->
    if !tacdbg then
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state);
    let goals, smt_goals = E.unembed_state ps.main_context embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run (t (unembed_b b)) ps in
    Some (E.embed_result res embed_a t_a)
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_2 (ps:proofstate)
                               (t:'a -> 'b -> tac<'c>) (unembed_a:term -> 'a) (unembed_b:term -> 'b)
                               (embed_c:'c -> term) (t_c:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (embedded_state, _)] ->
    if !tacdbg then
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state);
    let goals, smt_goals = E.unembed_state ps.main_context embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run (t (unembed_a a) (unembed_b b)) ps in
    Some (E.embed_result res embed_c t_c)
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let grewrite_interpretation (ps:proofstate) (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(et1, _); (et2, _); (embedded_state, _)] ->
    let goals, smt_goals = E.unembed_state ps.main_context embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run (grewrite_impl (type_of_embedded et1) (type_of_embedded et2) (unembed_term et1) (unembed_term et2)) ps in
    Some (E.embed_result res embed_unit FStar.TypeChecker.Common.t_unit)
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let rec primitive_steps ps : list<N.primitive_step> =
    let mk nm arity interpretation =
      let nm = E.fstar_tactics_lid nm in {
      N.name=nm;
      N.arity=arity;
      N.strong_reduction_ok=false;
      N.interpretation=(fun _rng args -> interpretation nm args)
    } in
    let mk_refl nm arity interpretation =
      let nm = FStar.Reflection.Data.fstar_refl_lid nm in {
      N.name=nm;
      N.arity=arity;
      N.strong_reduction_ok=false;
      N.interpretation=(fun _rng args -> interpretation nm args)
    } in
    let binders_of_env_int nm args : option<term> =
        match args with
        | [(e, _)] -> Some (embed_binders (Env.all_binders (E.unembed_env ps.main_context e)))
        | _ -> failwith (Util.format2 "Unexpected application %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))
    in
    [ mk "__forall_intros" 1 (mk_tactic_interpretation_0 ps intros embed_binders   FStar.Reflection.Data.fstar_refl_binders);
      mk "__implies_intro" 1 (mk_tactic_interpretation_0 ps imp_intro embed_binder FStar.Reflection.Data.fstar_refl_binder);
      mk "__trivial"  1 (mk_tactic_interpretation_0 ps trivial embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__revert"  1 (mk_tactic_interpretation_0 ps revert embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__clear"   1 (mk_tactic_interpretation_0 ps clear embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__split"   1 (mk_tactic_interpretation_0 ps split embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__merge"   1 (mk_tactic_interpretation_0 ps merge_sub_goals embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__rewrite" 2 (mk_tactic_interpretation_1 ps rewrite unembed_binder embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__smt"     1 (mk_tactic_interpretation_0 ps smt embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__exact"   2 (mk_tactic_interpretation_1 ps exact unembed_term embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__apply_lemma" 2 (mk_tactic_interpretation_1 ps apply_lemma unembed_term embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__visit"   2 (mk_tactic_interpretation_1 ps visit
                                                (unembed_tactic_0 unembed_unit)
                                                embed_unit
                                                FStar.TypeChecker.Common.t_unit);
      mk "__focus"   2  (mk_tactic_interpretation_1 ps focus_cur_goal
                                                (unembed_tactic_0 unembed_unit)
                                                embed_unit
                                                FStar.TypeChecker.Common.t_unit);
      mk "__seq"     3 (mk_tactic_interpretation_2 ps seq
                                            (unembed_tactic_0 unembed_unit)
                                            (unembed_tactic_0 unembed_unit)
                                            embed_unit
                                            FStar.TypeChecker.Common.t_unit);

      //TODO: this is more well-suited to be in FStar.Reflection
      //mk1 "__binders_of_env" Env.all_binders unembed_env embed_binders;
      mk_refl ["Syntax";"__binders_of_env"]  1 binders_of_env_int;

      mk "__print"           2 (mk_tactic_interpretation_1 ps (fun x -> ret (tacprint x)) unembed_string embed_unit
                                                              FStar.TypeChecker.Common.t_unit);
      mk "__dump"            2 (mk_tactic_interpretation_1 ps print_proof_state unembed_string embed_unit FStar.TypeChecker.Common.t_unit);
      mk "__grewrite"        3 (grewrite_interpretation ps)
    ]@reflection_primops

//F* version: and unembed_tactic_0 (#b:Type) (unembed_b:term -> b) (embedded_tac_b:term) : tac b =
and unembed_tactic_0<'b> (unembed_b:term -> 'b) (embedded_tac_b:term) : tac<'b> =
    bind get (fun proof_state ->
    let tm = S.mk_Tm_app embedded_tac_b
                         [S.as_arg (E.embed_state (proof_state.goals, []))]
                          None
                          Range.dummyRange in
    let steps = [N.Reify; N.Beta; N.UnfoldUntil Delta_constant; N.Zeta; N.Iota; N.Primops] in
    bind (mlog <| (fun _ -> BU.print1 "Starting normalizer with %s\n" (Print.term_to_string tm))) (fun _ ->
    let result = N.normalize_with_primitive_steps (primitive_steps proof_state) steps proof_state.main_context tm in
    bind (mlog <| (fun _ -> BU.print1 "Reduced tactic: got %s\n" (Print.term_to_string result))) (fun _ ->
    match E.unembed_result proof_state.main_context result unembed_b with
    | Inl (b, (goals, smt_goals)) ->
        bind dismiss (fun _ ->
        bind (add_goals goals) (fun _ ->
        bind (add_smt_goals smt_goals) (fun _ ->
        ret b)))

    | Inr (msg, (goals, smt_goals)) ->
        bind dismiss (fun _ ->
        bind (add_goals goals) (fun _ ->
        bind (add_smt_goals smt_goals) (fun _ ->
        fail msg))))))

let evaluate_user_tactic : tac<unit>
    = with_cur_goal (fun goal ->
      bind get (fun proof_state ->
          let hd, args = U.head_and_args goal.goal_ty in
          match (U.un_uinst hd).n, args with
          | Tm_fvar fv, [(tactic, _); (assertion, _)]
                when S.fv_eq_lid fv E.by_tactic_lid ->
            focus_cur_goal
            (bind (replace_cur ({goal with goal_ty=assertion})) (fun _ ->
                   unembed_tactic_0 unembed_unit tactic))
          | _ ->
            fail "Not a user tactic"))

let by_tactic_interp (e:Env.env) (t:term) : term * list<goal> =
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(tactic, _); (assertion, _)] when S.fv_eq_lid fv E.by_tactic_lid ->
        begin
        // kinda unclean
        match run (unembed_tactic_0 unembed_unit tactic) (proofstate_of_goal_ty e assertion) with
        | Success (_, ps) ->
            (FStar.Syntax.Util.t_true, ps.goals@ps.smt_goals)
        | Failed (s,ps) ->
            raise (FStar.Errors.Error ("user tactic failed: \"" ^ s ^ "\"", tactic.pos))
        end
    | _ ->
        (t, [])

let rec traverse (f:Env.env -> term -> term * list<goal>) (e:Env.env) (t:term)
        : term * list<goal> =
    let (tn', gs) =
        match (SS.compress t).n with
        | Tm_uinst (t,us) -> let (t',gs) = traverse f e t in
                             (Tm_uinst (t', us), gs)
        | Tm_meta (t, m) -> let (t', gs) = traverse f e t in
                            (Tm_meta (t', m), gs)
        | Tm_app ({ n = Tm_fvar fv }, [(p,_); (q,_)]) when S.fv_eq_lid fv FStar.Syntax.Const.imp_lid ->
               let x = S.new_bv None p in
               let (q',gs) = traverse f (Env.push_bv e x) q in
               ((U.mk_imp p q').n, gs)
        | Tm_app (hd, args) ->
                let (hd', gs1) = traverse f e hd in
                let (as', gs2) = List.fold_right (fun (a,q) (as',gs) ->
                                                      let (a', gs') = traverse f e a in
                                                      ((a',q)::as', gs@gs'))
                                                 args ([], []) in
                (Tm_app (hd', as'), gs1@gs2)
        | Tm_abs (bs, t, k) ->
                // TODO: traverse types in bs and k?
                let bs, topen = SS.open_term bs t in
                let e' = Env.push_binders e bs in
                let (topen', gs) = traverse f e' topen in
                ((U.abs bs topen' k).n, gs)
        | x -> (x, []) in
    let t' = { t with n = tn' } in
    let t', gs' = f e t' in
    (t', gs@gs')

let preprocess (env:Env.env) (goal:term) : list<(Env.env * term)> =
    // Check if we should print debug output
    tacdbg := Env.debug env (Options.Other "Tac");
    if !tacdbg then
        BU.print1 "About to preprocess %s\n" (Print.term_to_string goal);
    let initial = (1, []) in
    let (t', gs) = traverse by_tactic_interp env goal in
    if !tacdbg then
        BU.print2 "Main goal simplified to: %s |- %s\n"
                (Env.all_binders env |> Print.binders_to_string ", ")
                (Print.term_to_string t');
    let s = initial in
    let s = List.fold_left (fun (n,gs) g ->
                 if !tacdbg then
                     BU.print2 "Got goal #%s: %s\n" (string_of_int n) (goal_to_string g);
                 let gt' = TcUtil.label ("Goal #" ^ string_of_int n) dummyRange g.goal_ty in
                 (n+1, (g.context, gt')::gs)) s gs in
    let (_, gs) = s in
    (env, t') :: gs
