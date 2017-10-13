#light "off"
module FStar.Tactics.Interpreter
open FStar
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Range

module Err = FStar.Errors
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module PC = FStar.Parser.Const
open FStar.TypeChecker.Env
module Env = FStar.TypeChecker.Env
module BU = FStar.Util
module U = FStar.Syntax.Util
module TcRel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module TcTerm = FStar.TypeChecker.TcTerm
module N = FStar.TypeChecker.Normalize
open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Tactics.Basic
module E = FStar.Tactics.Embedding
module Core = FStar.Tactics.Basic
open FStar.Syntax.Embeddings
open FStar.Reflection.Basic
open FStar.Reflection.Interpreter
module RD = FStar.Reflection.Data
open FStar.Tactics.Native

let tacdbg = BU.mk_ref false

let mk_tactic_interpretation_0 (t:tac<'a>) (embed_a:'a -> term) (t_a:typ) (nm:Ident.lid) (args:args) : option<term> =
 (*  We have: t () embedded_state
     The idea is to:
        1. unembed the state
        2. run the `t` tactic
        3. embed the result and final state and return it to the normalizer
  *)
  match args with
  | [(embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    log ps (fun () ->
    BU.print2 "Reached %s, args are: %s\n"
            (Ident.string_of_lid nm)
            (Print.args_to_string args));
    let res = run t ps in
    Some (E.embed_result ps res embed_a t_a))
  | _ ->
    failwith ("Unexpected application of tactic primitive")

let mk_tactic_interpretation_1 (t:'a -> tac<'r>) (unembed_a:term -> option<'a>)
                               (embed_r:'r -> term) (t_r:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(a, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    let res = run (t a) ps in
    Some (E.embed_result ps res embed_r t_r)))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_1_env (t:N.psc -> 'b -> tac<'a>)
                                   (unembed_b:term -> option<'b>)
                                   (embed_a:'a -> term) (t_a:typ)
                                   (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
  match args with
  | [(b, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_b b) (fun b ->
    let res = run (t psc b) ps in
    Some (E.embed_result ps res embed_a t_a)))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_2 (t:'a -> 'b -> tac<'r>)
                               (unembed_a:term -> option<'a>)
                               (unembed_b:term -> option<'b>)
                               (embed_r:'r -> term)
                               (t_r:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    BU.bind_opt (unembed_b b) (fun b ->
    let res = run (t a b) ps in
    Some (E.embed_result ps res embed_r t_r))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_3 (t:'a -> 'b -> 'c -> tac<'r>)
                               (unembed_a:term -> option<'a>)
                               (unembed_b:term -> option<'b>)
                               (unembed_c:term -> option<'c>)
                               (embed_r:'r -> term) (t_r:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    BU.bind_opt (unembed_b b) (fun b ->
    BU.bind_opt (unembed_c c) (fun c ->
    let res = run (t a b c) ps in
    Some (E.embed_result ps res embed_r t_r)))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_5 (t:'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
                               (unembed_a:term -> option<'a>)
                               (unembed_b:term -> option<'b>)
                               (unembed_c:term -> option<'c>)
                               (unembed_d:term -> option<'d>)
                               (unembed_e:term -> option<'e>)
                               (embed_r:'r -> term) (t_r:typ)
                               (nm:Ident.lid) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (d, _); (e, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    BU.bind_opt (unembed_b b) (fun b ->
    BU.bind_opt (unembed_c c) (fun c ->
    BU.bind_opt (unembed_d d) (fun d ->
    BU.bind_opt (unembed_e e) (fun e ->
    let res = run (t a b c d e) ps in
    Some (E.embed_result ps res embed_r t_r)))))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let step_from_native_step (s: native_primitive_step): N.primitive_step =
    { N.name=s.name;
      N.arity=s.arity;
      N.strong_reduction_ok=s.strong_reduction_ok;
      N.requires_binder_substitution = false;
      N.interpretation=(fun _psc args -> s.tactic args) }

let rec primitive_steps () : list<N.primitive_step> =
    let mk nm arity interpretation =
      let nm = E.fstar_tactics_lid' ["Builtins";nm] in {
      N.name=nm;
      N.arity=arity;
      N.strong_reduction_ok=false;
      N.requires_binder_substitution = false;
      N.interpretation=(fun _rng args -> interpretation nm args)
    } in
    let mk_env nm arity interpretation =
      let nm = E.fstar_tactics_lid' ["Builtins";nm] in {
      N.name=nm;
      N.arity=arity;
      N.strong_reduction_ok=false;
      N.requires_binder_substitution = true;
      N.interpretation=(fun psc args -> interpretation nm psc args)
    } in
    let native_tactics = list_all () in
    let native_tactics_steps = List.map step_from_native_step native_tactics in
    let mktac0 (name : string) (f : tac<'r>)
               (e_r : 'r -> term) (tr : typ) : N.primitive_step =
        mk name 1 (mk_tactic_interpretation_0 f e_r tr)
    in
    let mktac1 (name : string) (f : 'a -> tac<'r>)
               (u_a : term -> option<'a>)
               (e_r : 'r -> term) (tr : typ) : N.primitive_step =
        mk name 2 (mk_tactic_interpretation_1 f u_a e_r tr)
    in
    let mktac1_env (name : string) (f : N.psc -> 'a -> tac<'b>)
                   (u_a : term -> option<'a>) (e_b : 'b -> term) (tb : typ) : N.primitive_step =
        mk_env name 2 (mk_tactic_interpretation_1_env f u_a e_b tb)
    in
    let mktac2 (name : string) (f : 'a -> 'b -> tac<'r>)
               (u_a : term -> option<'a>) (u_b : term -> option<'b>)
               (e_r : 'r -> term) (tr : typ) : N.primitive_step =
        mk name 3 (mk_tactic_interpretation_2 f u_a u_b e_r tr)
    in
    let mktac3 (name : string) (f : 'a -> 'b -> 'c -> tac<'r>)
               (u_a : term -> option<'a>) (u_b : term -> option<'b>) (u_c : term -> option<'c>)
               (e_r : 'r -> term) (tr : typ) : N.primitive_step =
        mk name 4 (mk_tactic_interpretation_3 f u_a u_b u_c e_r tr)
    in
    let mktac5 (name : string) (f : 'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
               (u_a : term -> option<'a>) (u_b : term -> option<'b>) (u_c : term -> option<'c>)
               (u_d : term -> option<'d>) (u_e : term -> option<'e>)
               (e_r : 'r -> term) (tr : typ) : N.primitive_step =
        mk name 6 (mk_tactic_interpretation_5 f u_a u_b u_c u_d u_e e_r tr)
    in
    let decr_depth_interp rng (args : args) =
        match args with
        | [(ps, _)] ->
            bind_opt (E.unembed_proofstate ps) (fun ps ->
            Some (E.embed_proofstate (decr_depth ps)))

        | _ -> failwith "Unexpected application of decr_depth"
    in
    let decr_depth_step : N.primitive_step =
        {N.name = Ident.lid_of_str "FStar.Tactics.Types.decr_depth";
         N.arity = 1;
         N.strong_reduction_ok = false;
         N.requires_binder_substitution = false;
         N.interpretation = decr_depth_interp
         }
    in
    let incr_depth_interp rng (args : args) =
        match args with
        | [(ps, _)] ->
            bind_opt (E.unembed_proofstate ps) (fun ps ->
            Some (E.embed_proofstate (incr_depth ps)))
        | _ -> failwith "Unexpected application of incr_depth"
    in
    let incr_depth_step : N.primitive_step =
        {N.name = Ident.lid_of_str "FStar.Tactics.Types.incr_depth";
         N.arity = 1;
         N.strong_reduction_ok = false;
         N.requires_binder_substitution = false;
         N.interpretation = incr_depth_interp
         }
    in
    let tracepoint_interp rng (args : args) =
        match args with
        | [(ps, _)] ->
            bind_opt (E.unembed_proofstate ps) (fun ps ->
            tracepoint ps;
            Some U.exp_unit)
        | _ -> failwith "Unexpected application of tracepoint"
    in
    let tracepoint_step : N.primitive_step =
        let nm = Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
        {N.name = nm;
         N.arity = 1;
         N.strong_reduction_ok = false;
         N.requires_binder_substitution = false;
         N.interpretation = tracepoint_interp
        }
    in
    [
      // When we want an identity unembedding, we use `Some`.
      // This is useful when, say, unembedding types for polymorphic tactics, due to our
      // parametricity argument.
      mktac0 "__trivial"       trivial embed_unit t_unit;
      mktac2 "__trytac"        (fun _ -> trytac) Some (unembed_tactic_0' Some) (embed_option (fun t -> t) t_unit) t_unit;
      mktac0 "__intro"         intro embed_binder RD.fstar_refl_binder;
      mktac0 "__intro_rec"     intro_rec (embed_pair
                                              embed_binder RD.fstar_refl_binder
                                              embed_binder RD.fstar_refl_binder)
                                         (E.pair_typ RD.fstar_refl_binder RD.fstar_refl_binder);
      mktac1 "__norm"          norm (unembed_list unembed_norm_step) embed_unit t_unit;
      mktac3 "__norm_term_env" norm_term_env unembed_env (unembed_list unembed_norm_step) unembed_term embed_term S.t_term;
      mktac2 "__rename_to"     rename_to unembed_binder unembed_string embed_unit t_unit;
      mktac1 "__binder_retype" binder_retype unembed_binder embed_unit t_unit;
      mktac0 "__revert"        revert embed_unit t_unit;
      mktac0 "__clear_top"     clear_top embed_unit t_unit;
      mktac1 "__clear"         clear unembed_binder embed_unit t_unit;
      mktac1 "__rewrite"       rewrite unembed_binder embed_unit t_unit;
      mktac0 "__smt"           smt embed_unit t_unit;
      mktac1 "__exact"         exact unembed_term embed_unit t_unit;
      mktac1 "__apply"         (apply  true) unembed_term embed_unit t_unit;
      mktac1 "__apply_raw"     (apply false) unembed_term embed_unit t_unit;
      mktac1 "__apply_lemma"   apply_lemma unembed_term embed_unit t_unit;
      // A tac 5... oh my...
      mktac5 "__divide"        (fun _ _ -> divide) Some Some unembed_int (unembed_tactic_0' Some) (unembed_tactic_0' Some)
                                                            (embed_pair (fun t -> t) t_unit (fun t -> t) t_unit) t_unit;
      mktac1 "__set_options"   set_options unembed_string embed_unit t_unit;
      mktac2 "__seq"           seq (unembed_tactic_0' unembed_unit) (unembed_tactic_0' unembed_unit) embed_unit t_unit;

      mktac1 "__tc"            tc unembed_term embed_term S.t_term;
      mktac1 "__unshelve"      unshelve unembed_term embed_unit t_unit;
      mktac2 "__unquote"       unquote Some unembed_term (fun t -> t) t_unit;

      mktac1 "__prune"         prune unembed_string embed_unit t_unit;
      mktac1 "__addns"         addns unembed_string embed_unit t_unit;

      mktac1 "__print"         (fun x -> ret (tacprint x)) unembed_string embed_unit t_unit;
      mktac1_env "__dump"      print_proof_state unembed_string embed_unit t_unit;
      mktac1_env "__dump1"     print_proof_state1 unembed_string embed_unit t_unit;

      mktac2 "__pointwise"     pointwise E.unembed_direction (unembed_tactic_0' unembed_unit) embed_unit t_unit;
      mktac0 "__trefl"         trefl embed_unit t_unit;
      mktac0 "__later"         later embed_unit t_unit;
      mktac0 "__dup"           dup embed_unit t_unit;
      mktac0 "__flip"          flip embed_unit t_unit;
      mktac0 "__qed"           qed embed_unit t_unit;
      mktac1 "__cases"         cases unembed_term (embed_pair
                                                      embed_term S.t_term
                                                      embed_term S.t_term)
                                                  (E.pair_typ S.t_term S.t_term);

      mktac0 "__top_env"       top_env     embed_env RD.fstar_refl_env;
      mktac0 "__cur_env"       cur_env     embed_env RD.fstar_refl_env;
      mktac0 "__cur_goal"      cur_goal'   embed_term S.t_term;
      mktac0 "__cur_witness"   cur_witness embed_term S.t_term;

      mktac2 "__uvar_env"      uvar_env unembed_env (unembed_option unembed_term) embed_term S.t_term;
      mktac2 "__unify"         unify unembed_term unembed_term embed_bool t_bool;
      mktac3 "__launch_process" launch_process unembed_string unembed_string unembed_string embed_string t_string;
      decr_depth_step;
      incr_depth_step;
      tracepoint_step;
    ]@reflection_primops @native_tactics_steps

// Please note, these markers are for some makefile magic that tweaks this function in the OCaml output

//IN F*: and unembed_tactic_0 (#b:Type) (unembed_b:term -> option b) (embedded_tac_b:term) : tac b =
and unembed_tactic_0<'b> (unembed_b:term -> option<'b>) (embedded_tac_b:term) : tac<'b> = //JUST FSHARP
    bind get (fun proof_state ->
    let tm = S.mk_Tm_app embedded_tac_b
                         [S.as_arg (E.embed_proofstate proof_state)]
                          None
                          Range.dummyRange in

    // Why not WHNF? While we don't care about strong reduction we need more than head
    // normal form due to primitive steps. Consider `norm (steps 2)`: we need to normalize
    // `steps 2` before caling norm, or it will fail to unembed the set of steps. Further,
    // at this moment at least, the normalizer will not call into any step of arity > 1.
    let steps = [N.Reify; N.UnfoldUntil Delta_constant; N.UnfoldTac; N.Primops] in
    if !tacdbg then
        BU.print1 "Starting normalizer with %s\n" (Print.term_to_string tm);
    let result = N.normalize_with_primitive_steps (primitive_steps ()) steps proof_state.main_context tm in
    if !tacdbg then
        BU.print1 "Reduced tactic: got %s\n" (Print.term_to_string result);
    match E.unembed_result proof_state result unembed_b with
    | Some (Inl (b, ps)) ->
        bind (set ps) (fun _ -> ret b)

    | Some (Inr (msg, ps)) ->
        bind (set ps) (fun _ -> fail msg)

    | None ->
        raise (Err.Error (BU.format1 "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s" (Print.term_to_string result), proof_state.main_context.range))
    )
//IN F*: and unembed_tactic_0' (#b:Type) (unembed_b:term -> option b) (embedded_tac_b:term) : option (tac b) =
and unembed_tactic_0'<'b> (unembed_b:term -> option<'b>) (embedded_tac_b:term) : option<(tac<'b>)> = //JUST FSHARP
    Some <| unembed_tactic_0 unembed_b embedded_tac_b

let report_implicits ps (is : Env.implicits) : unit =
    let errs = List.map (fun (r, _, uv, _, ty, rng) ->
                (BU.format3 ("Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")")
                             (Print.uvar_to_string uv) (Print.term_to_string ty) r,
                 rng)) is in
    match errs with
    | [] -> ()
    | hd::tl -> begin
        dump_proofstate ps "failing due to uninstantiated implicits";
        // A trick to print each error exactly once.
        Err.add_errors tl;
        raise (Err.Error hd)
    end

let run_tactic_on_typ (tactic:term) (env:env) (typ:typ) : list<goal> // remaining goals
                                                        * term // witness
                                                        =
    // This bit is really important: a typechecked tactic can contain many uvar redexes
    // that make normalization SUPER slow (probably exponential). Doing this first pass
    // gets rid of those redexes and leaves a much smaller term, which performs a lot better.
    if !tacdbg then
        BU.print1 "About to reduce uvars on: %s\n" (Print.term_to_string tactic);
    let tactic = N.reduce_uvar_solutions env tactic in
    if !tacdbg then
        BU.print1 "About to check tactic term: %s\n" (Print.term_to_string tactic);
    let tactic, _, g = TcTerm.tc_reified_tactic env tactic in
    TcRel.force_trivial_guard env g;
    Err.stop_if_err ();
    let tau = unembed_tactic_0 unembed_unit tactic in
    let env, _ = Env.clear_expected_typ env in
    let env = { env with Env.instantiate_imp = false } in
    let ps, w = proofstate_of_goal_ty env typ in
    if !tacdbg then
        BU.print_string "Running tactic.\n";
    match run tau ps with
    | Success (_, ps) ->
        if !tacdbg then
            BU.print1 "Tactic generated proofterm %s\n" (Print.term_to_string w); //FIXME: Is this right?
        List.iter (fun g -> if is_irrelevant g
                            then if TcRel.teq_nosmt g.context g.witness U.exp_unit
                                 then ()
                                 else failwith (BU.format1 "Irrelevant tactic witness does not unify with (): %s" (Print.term_to_string g.witness))
                            else ())
                  (ps.goals @ ps.smt_goals);

        // Check that all implicits are instantiated. This will also typecheck
        // the implicits, so make it do a lax check because we certainly
        // do not want to repeat all of the reasoning that took place in tactics.
        // It would also most likely fail.
        let g = {TcRel.trivial_guard with Env.implicits=ps.all_implicits} in
        let g = TcRel.solve_deferred_constraints env g |> TcRel.resolve_implicits_tac in
        report_implicits ps g.implicits;
        (ps.goals@ps.smt_goals, w)

    | Failed (s, ps) ->
        dump_proofstate ps "at the time of failure";
        raise (Err.Error (BU.format1 "user tactic failed: %s" s, typ.pos))

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
    // Check that all goals left are irrelevant. We don't need to check their
    // validity, as we will typecheck the witness independently.
    if List.existsML (fun g -> not (Option.isSome (getprop g.context g.goal_ty))) gs
    then raise (Err.Error ("synthesis left open goals", typ.pos))
    else w
