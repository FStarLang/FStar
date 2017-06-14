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
module TcRel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module N = FStar.TypeChecker.Normalize
open FStar.Tactics.Basic
module E = FStar.Tactics.Embedding
module Core = FStar.Tactics.Basic
open FStar.Reflection.Basic
open FStar.Reflection.Interpreter
module RD = FStar.Reflection.Data

let tacdbg = BU.mk_ref false

let t_unit = FStar.TypeChecker.Common.t_unit

let mk_tactic_interpretation_0 (ps:proofstate) (t:tac<'a>) (embed_a:'a -> term) (t_a:typ) (nm:Ident.lid) (args:args) : option<term> =
 (*  We have: t () embedded_state
     The idea is to:
        1. unembed the state
        2. run the `t` tactic
        3. embed the result and final state and return it to the normalizer
  *)
  match args with
  | [(embedded_state, _)] ->
    log ps (fun () ->
    BU.print2 "Reached %s, args are: %s\n"
            (Ident.string_of_lid nm)
            (Print.args_to_string args));
    let goals, smt_goals = E.unembed_state ps embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run t ps in
    Some (E.embed_result ps res embed_a t_a)
  | _ ->
    failwith ("Unexpected application of tactic primitive")

let mk_tactic_interpretation_1 (ps:proofstate)
                               (t:'b -> tac<'a>) (unembed_b:term -> 'b)
                               (embed_a:'a -> term) (t_a:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(b, _); (embedded_state, _)] ->
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    let goals, smt_goals = E.unembed_state ps embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run (t (unembed_b b)) ps in
    Some (E.embed_result ps res embed_a t_a)
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_2 (ps:proofstate)
                               (t:'a -> 'b -> tac<'c>) (unembed_a:term -> 'a) (unembed_b:term -> 'b)
                               (embed_c:'c -> term) (t_c:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (embedded_state, _)] ->
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    let goals, smt_goals = E.unembed_state ps embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run (t (unembed_a a) (unembed_b b)) ps in
    Some (E.embed_result ps res embed_c t_c)
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let rec primitive_steps ps : list<N.primitive_step> =
    let mk nm arity interpretation =
      let nm = E.fstar_tactics_lid' ["Builtins";nm] in {
      N.name=nm;
      N.arity=arity;
      N.strong_reduction_ok=false;
      N.interpretation=(fun _rng args -> interpretation nm args)
    } in
    let mk_refl nm arity interpretation =
      let nm = RD.fstar_refl_lid nm in {
      N.name=nm;
      N.arity=arity;
      N.strong_reduction_ok=false;
      N.interpretation=(fun _rng args -> interpretation nm args)
    } in
    let mktac0 (name : string) (f : tac<'a>) (e_a : 'a -> term) (ta : typ) : N.primitive_step =
        mk name 1 (mk_tactic_interpretation_0 ps f e_a ta)
    in
    let mktac1 (name : string) (f : 'a -> tac<'b>) (u_a : term -> 'a) (e_b : 'b -> term) (tb : typ) : N.primitive_step =
        mk name 2 (mk_tactic_interpretation_1 ps f u_a e_b tb)
    in
    let mktac2 (name : string) (f : 'a -> 'b -> tac<'c>) (u_a : term -> 'a) (u_b : term -> 'b) (e_c : 'c -> term) (tc : typ) : N.primitive_step =
        mk name 3 (mk_tactic_interpretation_2 ps f u_a u_b e_c tc)
    in
    let binders_of_env_int nm args : option<term> =
        match args with
        | [(e, _)] -> Some (embed_binders (Env.all_binders (E.unembed_env ps e)))
        | _ -> failwith (Util.format2 "Unexpected application %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))
    in
    [
      mktac0 "__trivial"       trivial embed_unit t_unit;
      mktac2 "__trytac"        (fun _ -> trytac) (fun t-> t) (unembed_tactic_0 (fun t -> t)) (embed_option (fun t -> t) t_unit) t_unit;
      mktac0 "__intro"         intro embed_binder RD.fstar_refl_binder;
      mktac1 "__norm"          norm (unembed_list unembed_norm_step) embed_unit t_unit;
      mktac0 "__revert"        revert embed_unit t_unit;
      mktac0 "__clear"         clear embed_unit t_unit;
      mktac1 "__rewrite"       rewrite unembed_binder embed_unit t_unit;
      mktac0 "__smt"           smt embed_unit t_unit;
      mktac1 "__exact"         exact unembed_term embed_unit t_unit;
      mktac1 "__exact_lemma"   exact_lemma unembed_term embed_unit t_unit;
      mktac1 "__apply"         apply unembed_term embed_unit t_unit;
      mktac1 "__apply_lemma"   apply_lemma unembed_term embed_unit t_unit;
      mktac1 "__focus"         focus_cur_goal (unembed_tactic_0 unembed_unit) embed_unit t_unit;
      mktac2 "__seq"           seq (unembed_tactic_0 unembed_unit) (unembed_tactic_0 unembed_unit) embed_unit t_unit;

      mktac1 "__prune"         prune unembed_string embed_unit t_unit;
      mktac1 "__addns"         addns unembed_string embed_unit t_unit;

      mktac1 "__print"         (fun x -> ret (tacprint x)) unembed_string embed_unit t_unit;
      mktac1 "__dump"          print_proof_state unembed_string embed_unit t_unit;
      mktac1 "__dump1"         print_proof_state1 unembed_string embed_unit t_unit;

      mktac1 "__pointwise"     pointwise (unembed_tactic_0 unembed_unit) embed_unit t_unit;
      mktac0 "__trefl"         trefl embed_unit t_unit;
      mktac0 "__later"         later embed_unit t_unit;
      mktac0 "__flip"          flip embed_unit t_unit;
      mktac0 "__qed"           qed embed_unit t_unit;
      mktac1 "__cases"         cases unembed_term (embed_pair
                                                      embed_term RD.fstar_refl_term
                                                      embed_term RD.fstar_refl_term)
                                                  (E.pair_typ RD.fstar_refl_term RD.fstar_refl_term);

      //TODO: this is more well-suited to be in FStar.Reflection
      //mk1 "__binders_of_env" Env.all_binders unembed_env embed_binders;
      mk_refl ["Syntax";"__binders_of_env"]  1 binders_of_env_int;

      mktac0 "__cur_env"       cur_env     (E.embed_env ps) RD.fstar_refl_env;
      mktac0 "__cur_goal"      cur_goal'   embed_term  RD.fstar_refl_term;
      mktac0 "__cur_witness"   cur_witness embed_term  RD.fstar_refl_term;
    ]@reflection_primops

// Please note, there is some makefile magic to tweak this function in the OCaml output,
// BESIDES the markers you see right here. If you change anything, be sure to revise it.

//IN F*: and unembed_tactic_0 (#b:Type) (unembed_b:term -> b) (embedded_tac_b:term) : tac b =
and unembed_tactic_0<'b> (unembed_b:term -> 'b) (embedded_tac_b:term) : tac<'b> = //JUST FSHARP
    bind get (fun proof_state ->
    let tm = S.mk_Tm_app embedded_tac_b
                         [S.as_arg (E.embed_state proof_state (proof_state.goals, proof_state.smt_goals))]
                          None
                          Range.dummyRange in
    let steps = [N.Reify; N.UnfoldUntil Delta_constant; N.UnfoldTac; N.Primops] in
    bind (mlog <| (fun _ -> BU.print1 "Starting normalizer with %s\n" (Print.term_to_string tm))) (fun _ ->
    let result = N.normalize_with_primitive_steps (primitive_steps proof_state) steps proof_state.main_context tm in
    bind (mlog <| (fun _ -> BU.print1 "Reduced tactic: got %s\n" (Print.term_to_string result))) (fun _ ->
    match E.unembed_result proof_state result unembed_b with
    | Inl (b, (goals, smt_goals)) ->
        bind dismiss_all (fun _ ->
        bind (add_goals goals) (fun _ ->
        bind (add_smt_goals smt_goals) (fun _ ->
        ret b)))

    | Inr (msg, (goals, smt_goals)) ->
        bind dismiss_all (fun _ ->
        bind (add_goals goals) (fun _ ->
        bind (add_smt_goals smt_goals) (fun _ ->
        fail msg))))))

// Polarity
type pol = | Pos | Neg

let flip p = match p with | Pos -> Neg | Neg -> Pos

let by_tactic_interp (pol:pol) (e:Env.env) (t:term) : term * list<goal> =
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with

    | Tm_fvar fv, [(rett, _); (tactic, _); (assertion, _)] when S.fv_eq_lid fv E.by_tactic_lid && pol = Neg ->
        (assertion, []) // Peel away tactics in negative positions, they're assumptions!

    | Tm_fvar fv, [(rett, _); (tactic, _); (assertion, _)] when S.fv_eq_lid fv E.by_tactic_lid && pol = Pos ->
        // kinda unclean
        let ps = proofstate_of_goal_ty e assertion in
        let w = (List.hd ps.goals).witness in
        let r = try run (unembed_tactic_0 unembed_unit tactic) ps
                with | TacFailure s -> Failed ("EXCEPTION: " ^ s, ps)
        in
        begin match r with
        | Success (_, ps) ->
            if !tacdbg then
                BU.print1 "Tactic generated proofterm %s\n"
                                (Print.term_to_string w);
            List.iter (fun g -> if is_irrelevant g
                                then if TcRel.teq_nosmt g.context g.witness SC.exp_unit
                                     then ()
                                     else failwith (BU.format1 "Irrelevant tactic witness does not unify with (): %s" (Print.term_to_string g.witness))
                                else ())
                      (ps.goals @ ps.smt_goals);
            let g = {TcRel.trivial_guard with Env.implicits=ps.all_implicits} in
            let _ = TcRel.discharge_guard_no_smt e g in
            (FStar.Syntax.Util.t_true, ps.goals@ps.smt_goals)
        | Failed (s, ps) ->
            raise (FStar.Errors.Error (BU.format1 "user tactic failed: %s" s, assertion.pos))
        end
    | _ ->
        (t, [])

let rec traverse (f: pol -> Env.env -> term -> term * list<goal>) (pol:pol) (e:Env.env) (t:term) : term * list<goal> =
    let (tn', gs) =
        match (SS.compress t).n with
        | Tm_uinst (t,us) -> let (t',gs) = traverse f pol e t in
                             (Tm_uinst (t', us), gs)
        | Tm_meta (t, m) -> let (t', gs) = traverse f pol e t in
                            (Tm_meta (t', m), gs)

        | Tm_app ({ n = Tm_fvar fv }, [(p,_); (q,_)]) when S.fv_eq_lid fv FStar.Syntax.Const.imp_lid ->
               let x = S.new_bv None p in
               let (p', gs1) = traverse f (flip pol) (Env.push_bv e x) p in
               let (q', gs2) = traverse f       pol  (Env.push_bv e x) q in
               ((U.mk_imp p' q').n, gs1@gs2)

        | Tm_app (hd, args) ->
                let (hd', gs1) = traverse f pol e hd in
                let (as', gs2) = List.fold_right (fun (a,q) (as',gs) ->
                                                      let (a', gs') = traverse f pol e a in
                                                      ((a',q)::as', gs@gs'))
                                                 args ([], []) in
                (Tm_app (hd', as'), gs1@gs2)
        | Tm_abs (bs, t, k) ->
                // TODO: traverse k?
                let bs, topen = SS.open_term bs t in
                let e' = Env.push_binders e bs in
                let bs, gs1 = List.unzip <| List.map (fun (bv, aq) ->
                                                   let (s', gs) = traverse f (flip pol) e bv.sort
                                                   in (({bv with sort = s'}, aq), gs)
                                                ) bs
                in
                let gs1 = List.flatten gs1 in
                let (topen', gs2) = traverse f pol e' topen in
                ((U.abs bs topen' k).n, gs1@gs2)
        | x -> (x, []) in
    let t' = { t with n = tn' } in
    let t', gs' = f pol e t' in
    (t', gs@gs')

let getprop (e:env) (t:term) : option<term> =
    let tn = N.normalize [N.WHNF; N.UnfoldUntil Delta_constant] e t in
    match U.un_squash tn with
    | Some t' -> Some t'
    | None ->
        // Check for an equality, since the delta depth is wrong... (TODO: fix that)
        let hd, _ = U.head_and_args tn in
        match (U.un_uinst hd).n with
        | Tm_fvar fv when S.fv_eq_lid fv SC.eq2_lid -> Some t
        | _ -> None

let preprocess (env:Env.env) (goal:term) : list<(Env.env * term)> =
    tacdbg := Env.debug env (Options.Other "Tac");
    if !tacdbg then
        BU.print2 "About to preprocess %s |= %s\n"
                        (Env.all_binders env |> Print.binders_to_string ",")
                        (Print.term_to_string goal);
    let env, _ = Env.clear_expected_typ env in
    let env = { env with Env.instantiate_imp = false } in
    let initial = (1, []) in
    let (t', gs) = traverse by_tactic_interp Pos env goal in
    if !tacdbg then
        BU.print2 "Main goal simplified to: %s |- %s\n"
                (Env.all_binders env |> Print.binders_to_string ", ")
                (Print.term_to_string t');
    let s = initial in
    let s = List.fold_left (fun (n,gs) g ->
                 let phi = match getprop g.context g.goal_ty with
                           | None -> failwith (BU.format1 "Tactic returned proof-relevant goal: %s" (Print.term_to_string g.goal_ty))
                           | Some phi -> phi
                 in
                 if not (TcRel.teq_nosmt g.context g.witness SC.exp_unit)
                 then failwith (BU.format1 "Irrelevant tactic witness does not unify with (): %s"
                         (Print.term_to_string g.witness))
                 else
                 if !tacdbg then
                     BU.print2 "Got goal #%s: %s\n" (string_of_int n) (goal_to_string g);
                 let gt' = TcUtil.label ("Could not prove goal #" ^ string_of_int n) dummyRange phi in
                 (n+1, (g.context, gt')::gs)) s gs in
    let (_, gs) = s in
    (env, t') :: gs

let reify_tactic (a : term) : term =
    let r = S.mk_Tm_uinst (S.fv_to_tm (S.lid_as_fv SC.reify_tactic_lid Delta_equational None)) [U_zero] in
    mk_Tm_app r [S.iarg t_unit; S.as_arg a] None a.pos

let synth (env:Env.env) (typ:typ) (tau:term) : term =
    let ps = proofstate_of_goal_ty env typ in
    let w = (List.hd ps.goals).witness in
    let r = try run (unembed_tactic_0 unembed_unit (reify_tactic tau)) ps
            with | TacFailure s -> Failed ("EXCEPTION: " ^ s, ps)
    in
    begin match r with
    | Success (_, ps) ->
        if !tacdbg then
            BU.print1 "Tactic generated proofterm %s\n"
                            (Print.term_to_string w);
        // TODO, check for others goals? Not really needed...
        let g = {TcRel.trivial_guard with Env.implicits=ps.all_implicits} in
        let _ = TcRel.discharge_guard_no_smt env g in
        w
    | Failed (s, ps) ->
        FStar.Errors.err typ.pos (BU.format1 "user tactic failed: %s" s);
        failwith "aborting"
    end
