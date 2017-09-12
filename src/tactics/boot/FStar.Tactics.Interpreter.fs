#light "off"
module FStar.Tactics.Interpreter
open FStar
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Range

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module PC = FStar.Parser.Const
module Env = FStar.TypeChecker.Env
module BU = FStar.Util
module U = FStar.Syntax.Util
module TcRel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module TcTerm = FStar.TypeChecker.TcTerm
module N = FStar.TypeChecker.Normalize
open FStar.Tactics.Basic
module E = FStar.Tactics.Embedding
module Core = FStar.Tactics.Basic
open FStar.Syntax.Embeddings
open FStar.Reflection.Basic
open FStar.Reflection.Interpreter
module RD = FStar.Reflection.Data
open FStar.Tactics.Native

let tacdbg = BU.mk_ref false

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
    let ps = E.unembed_proofstate ps embedded_state in
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
    let ps = E.unembed_proofstate ps embedded_state in
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
    let ps = E.unembed_proofstate ps embedded_state in
    let res = run (t (unembed_a a) (unembed_b b)) ps in
    Some (E.embed_result ps res embed_c t_c)
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_3 (ps:proofstate)
                               (t:'a -> 'b -> 'c -> tac<'d>) (unembed_a:term -> 'a) (unembed_b:term -> 'b) (unembed_c:term -> 'c)
                               (embed_d:'d -> term) (t_d:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (embedded_state, _)] ->
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    let ps = E.unembed_proofstate ps embedded_state in
    let res = run (t (unembed_a a) (unembed_b b) (unembed_c c)) ps in
    Some (E.embed_result ps res embed_d t_d)
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_5 (ps:proofstate)
                               (t:'a -> 'b -> 'c -> 'd -> 'e -> tac<'f>)
                               (unembed_a:term -> 'a) (unembed_b:term -> 'b) (unembed_c:term -> 'c)
                               (unembed_d:term -> 'd) (unembed_e:term -> 'e)
                               (embed_f:'f -> term) (t_f:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (d, _); (e, _); (embedded_state, _)] ->
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    let ps = E.unembed_proofstate ps embedded_state in
    let res = run (t (unembed_a a) (unembed_b b) (unembed_c c) (unembed_d d) (unembed_e e)) ps in
    Some (E.embed_result ps res embed_f t_f)
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let step_from_native_step (ps: proofstate) (s: native_primitive_step): N.primitive_step =
    { N.name=s.name;
      N.arity=s.arity;
      N.strong_reduction_ok=s.strong_reduction_ok;
      N.interpretation=(fun _rng args -> s.tactic ps args) }

let rec primitive_steps ps : list<N.primitive_step> =
    let mk nm arity interpretation =
      let nm = E.fstar_tactics_lid' ["Builtins";nm] in {
      N.name=nm;
      N.arity=arity;
      N.strong_reduction_ok=false;
      N.interpretation=(fun _rng args -> interpretation nm args)
    } in
    let native_tactics = list_all () in
    let native_tactics_steps = List.map (step_from_native_step ps) native_tactics in
    let mktac0 (name : string) (f : tac<'a>) (e_a : 'a -> term) (ta : typ) : N.primitive_step =
        mk name 1 (mk_tactic_interpretation_0 ps f e_a ta)
    in
    let mktac1 (name : string) (f : 'a -> tac<'b>) (u_a : term -> 'a) (e_b : 'b -> term) (tb : typ) : N.primitive_step =
        mk name 2 (mk_tactic_interpretation_1 ps f u_a e_b tb)
    in
    let mktac2 (name : string) (f : 'a -> 'b -> tac<'c>) (u_a : term -> 'a) (u_b : term -> 'b) (e_c : 'c -> term) (tc : typ) : N.primitive_step =
        mk name 3 (mk_tactic_interpretation_2 ps f u_a u_b e_c tc)
    in
    let mktac3 (name : string) (f : 'a -> 'b -> 'c -> tac<'d>) (u_a : term -> 'a) (u_b : term -> 'b) (u_c : term -> 'c)
                               (e_d : 'd -> term) (tc : typ) : N.primitive_step =
        mk name 4 (mk_tactic_interpretation_3 ps f u_a u_b u_c e_d tc)
    in
    let mktac5 (name : string) (f : 'a -> 'b -> 'c -> 'd -> 'e -> tac<'f>)
                               (u_a : term -> 'a) (u_b : term -> 'b) (u_c : term -> 'c)
                               (u_d : term -> 'd) (u_e : term -> 'e)
                               (e_f : 'f -> term) (tc : typ) : N.primitive_step =
        mk name 6 (mk_tactic_interpretation_5 ps f u_a u_b u_c u_d u_e e_f tc)
    in
    [
      mktac0 "__trivial"       trivial embed_unit t_unit;
      mktac2 "__trytac"        (fun _ -> trytac) (fun t-> t) (unembed_tactic_0 (fun t -> t)) (embed_option (fun t -> t) t_unit) t_unit;
      mktac0 "__intro"         intro embed_binder RD.fstar_refl_binder;
      mktac0 "__intro_rec"     intro_rec (embed_pair
                                              embed_binder RD.fstar_refl_binder
                                              embed_binder RD.fstar_refl_binder)
                                         (E.pair_typ RD.fstar_refl_binder RD.fstar_refl_binder);
      mktac1 "__norm"          norm (unembed_list unembed_norm_step) embed_unit t_unit;
      mktac2 "__norm_term"     norm_term (unembed_list unembed_norm_step) unembed_term embed_term RD.fstar_refl_term;
      mktac0 "__revert"        revert embed_unit t_unit;
      mktac0 "__clear"         clear embed_unit t_unit;
      mktac1 "__rewrite"       rewrite unembed_binder embed_unit t_unit;
      mktac0 "__smt"           smt embed_unit t_unit;
      mktac1 "__exact"         exact unembed_term embed_unit t_unit;
      mktac1 "__exact_lemma"   exact_lemma unembed_term embed_unit t_unit;
      mktac1 "__apply"         (apply  true) unembed_term embed_unit t_unit;
      mktac1 "__apply_raw"     (apply false) unembed_term embed_unit t_unit;
      mktac1 "__apply_lemma"   apply_lemma unembed_term embed_unit t_unit;
      // A tac 5... oh my...
      mktac5 "__divide"        (fun _ _ -> divide) (fun t -> t) (fun t -> t) unembed_int (unembed_tactic_0 (fun t -> t)) (unembed_tactic_0 (fun t -> t))
                                                            (embed_pair (fun t -> t) t_unit (fun t -> t) t_unit) t_unit;
      mktac1 "__set_options"   set_options unembed_string embed_unit t_unit;
      mktac2 "__seq"           seq (unembed_tactic_0 unembed_unit) (unembed_tactic_0 unembed_unit) embed_unit t_unit;

      mktac2 "__unquote"       unquote (fun t -> t) unembed_term (fun t -> t) t_unit;

      mktac1 "__prune"         prune unembed_string embed_unit t_unit;
      mktac1 "__addns"         addns unembed_string embed_unit t_unit;

      mktac1 "__print"         (fun x -> ret (tacprint x)) unembed_string embed_unit t_unit;
      mktac1 "__dump"          print_proof_state unembed_string embed_unit t_unit;
      mktac1 "__dump1"         print_proof_state1 unembed_string embed_unit t_unit;

      mktac1 "__pointwise"     pointwise (unembed_tactic_0 unembed_unit) embed_unit t_unit;
      mktac0 "__trefl"         trefl embed_unit t_unit;
      mktac0 "__later"         later embed_unit t_unit;
      mktac0 "__dup"           dup embed_unit t_unit;
      mktac0 "__flip"          flip embed_unit t_unit;
      mktac0 "__qed"           qed embed_unit t_unit;
      mktac1 "__cases"         cases unembed_term (embed_pair
                                                      embed_term RD.fstar_refl_term
                                                      embed_term RD.fstar_refl_term)
                                                  (E.pair_typ RD.fstar_refl_term RD.fstar_refl_term);

      mktac0 "__cur_env"       cur_env     embed_env RD.fstar_refl_env;
      mktac0 "__cur_goal"      cur_goal'   embed_term RD.fstar_refl_term;
      mktac0 "__cur_witness"   cur_witness embed_term RD.fstar_refl_term;

      mktac2 "__uvar_env"      uvar_env unembed_env (unembed_option unembed_term) embed_term RD.fstar_refl_term;
      mktac2 "__unify"         unify unembed_term unembed_term embed_bool t_bool;
      mktac3 "__launch_process" launch_process unembed_string unembed_string unembed_string embed_string t_string;
    ]@reflection_primops @native_tactics_steps

// Please note, these markers are for some makefile magic that tweaks this function in the OCaml output

//IN F*: and unembed_tactic_0 (#b:Type) (unembed_b:term -> b) (embedded_tac_b:term) : tac b =
and unembed_tactic_0<'b> (unembed_b:term -> 'b) (embedded_tac_b:term) : tac<'b> = //JUST FSHARP
    bind get (fun proof_state ->
    let tm = S.mk_Tm_app embedded_tac_b
                         [S.as_arg (E.embed_proofstate proof_state)]
                          None
                          Range.dummyRange in
    let steps = [N.Reify; N.UnfoldUntil Delta_constant; N.UnfoldTac; N.Primops] in
    bind (mlog <| (fun _ -> BU.print1 "Starting normalizer with %s\n" (Print.term_to_string tm))) (fun _ ->
    let result = N.normalize_with_primitive_steps (primitive_steps proof_state) steps proof_state.main_context tm in
    bind (mlog <| (fun _ -> BU.print1 "Reduced tactic: got %s\n" (Print.term_to_string result))) (fun _ ->
    match E.unembed_result proof_state result unembed_b with
    | Inl (b, ps) ->
        bind (set ps) (fun _ -> ret b)

    | Inr (msg, ps) ->
        bind (set ps) (fun _ -> fail msg)
    )))

let run_tactic_on_typ (tactic:term) (env:env) (typ:typ) : list<goal> // remaining goals, to be fed to SMT
                                                        * term // witness, in case it's needed, as in synthesis)
                                                        =
    let tactic, _, _ = TcTerm.tc_reified_tactic env tactic in
    let tau = unembed_tactic_0 unembed_unit tactic in
    let env, _ = Env.clear_expected_typ env in
    let env = { env with Env.instantiate_imp = false } in
    let ps, w = proofstate_of_goal_ty env typ in
    let r = try run tau ps
            with | TacFailure s -> Failed ("EXCEPTION: " ^ s, ps)
    in
    match r with
    | Success (_, ps) ->
        if !tacdbg then
            BU.print1 "Tactic generated proofterm %s\n" (Print.term_to_string w); //FIXME: Is this right?
        List.iter (fun g -> if is_irrelevant g
                            then if TcRel.teq_nosmt g.context g.witness U.exp_unit
                                 then ()
                                 else failwith (BU.format1 "Irrelevant tactic witness does not unify with (): %s" (Print.term_to_string g.witness))
                            else ())
                  (ps.goals @ ps.smt_goals);
        let g = {TcRel.trivial_guard with Env.implicits=ps.all_implicits} in
        // Check that all implicits are instantiated. This will also typecheck
        // the implicits, so make it do a lax check because we certainly
        // do not want to repeat all of the reasoning that took place in tactics.
        // It would also most likely fail.
        let g = TcRel.solve_deferred_constraints env g |> TcRel.resolve_implicits_lax in
        let _ = TcRel.force_trivial_guard env g in
        (ps.goals@ps.smt_goals, w)
    | Failed (s, ps) ->
        dump_proofstate ps "at the time of failure";
        raise (FStar.Errors.Error (BU.format1 "user tactic failed: %s" s, typ.pos))


// Polarity
type pol = | Pos | Neg

let flip p = match p with | Pos -> Neg | Neg -> Pos

let by_tactic_interp (pol:pol) (e:Env.env) (t:term) : term * list<goal> =
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with

    // by_tactic marker
    | Tm_fvar fv, [(rett, Some (Implicit _)); (tactic, None); (assertion, None)]
            when S.fv_eq_lid fv PC.by_tactic_lid ->
        if pol = Pos then
            let gs, _ = run_tactic_on_typ tactic e assertion in
            (FStar.Syntax.Util.t_true, gs)
        else
            (assertion, []) // Peel away tactics in negative positions, they're assumptions!

    // spinoff marker: simply spin off a query independently.
    // So, equivalent to `by_tactic idtac` without importing the (somewhat heavy) tactics module
    | Tm_fvar fv, [(assertion, None)]
            when S.fv_eq_lid fv PC.spinoff_lid ->
        if pol = Pos then
            (FStar.Syntax.Util.t_true, [fst <| goal_of_goal_ty e assertion])
        else
            (assertion, [])

    | _ ->
        (t, [])

let rec traverse (f: pol -> Env.env -> term -> term * list<goal>) (pol:pol) (e:Env.env) (t:term) : term * list<goal> =
    let (tn', gs) =
        match (SS.compress t).n with
        | Tm_uinst (t,us) -> let (t',gs) = traverse f pol e t in
                             (Tm_uinst (t', us), gs)
        | Tm_meta (t, m) -> let (t', gs) = traverse f pol e t in
                            (Tm_meta (t', m), gs)

        | Tm_app ({ n = Tm_fvar fv }, [(p,_); (q,_)]) when S.fv_eq_lid fv PC.imp_lid ->
               let x = S.new_bv None (U.mk_squash p) in
               let (p', gs1) = traverse f (flip pol)  e                p in
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
    U.un_squash tn

let preprocess (env:Env.env) (goal:term) : list<(Env.env * term * FStar.Options.optionstate)> =
    tacdbg := Env.debug env (Options.Other "Tac");
    if !tacdbg then
        BU.print2 "About to preprocess %s |= %s\n"
                        (Env.all_binders env |> Print.binders_to_string ",")
                        (Print.term_to_string goal);
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
                 if !tacdbg then
                     BU.print2 "Got goal #%s: %s\n" (string_of_int n) (goal_to_string g);
                 let gt' = TcUtil.label ("Could not prove goal #" ^ string_of_int n) goal.pos phi in
                 (n+1, (g.context, gt', g.opts)::gs)) s gs in
    let (_, gs) = s in
    // Use default opts for main goal
    (env, t', FStar.Options.peek ()) :: gs

let reify_tactic (a : term) : term =
    let r = S.mk_Tm_uinst (S.fv_to_tm (S.lid_as_fv PC.reify_tactic_lid Delta_equational None)) [U_zero] in
    mk_Tm_app r [S.iarg t_unit; S.as_arg a] None a.pos

let synth (env:Env.env) (typ:typ) (tau:term) : term =
    tacdbg := Env.debug env (Options.Other "Tac");
    let gs, w = run_tactic_on_typ (reify_tactic tau) env typ in
    match gs with
    | [] -> w
    | _::_ -> raise (FStar.Errors.Error ("synthesis left open goals", typ.pos))
