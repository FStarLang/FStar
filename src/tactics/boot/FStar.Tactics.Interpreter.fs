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
module Cfg = FStar.TypeChecker.Cfg
module N = FStar.TypeChecker.Normalize
module Env = FStar.TypeChecker.Env
open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Tactics.Basic
module E = FStar.Tactics.Embedding
module Core = FStar.Tactics.Basic
open FStar.Syntax.Embeddings
open FStar.Reflection.Basic
open FStar.Reflection.Interpreter
module RD = FStar.Reflection.Data
module RE = FStar.Reflection.Embeddings
module NRE = FStar.Reflection.NBEEmbeddings
module NBE = FStar.TypeChecker.NBE
module NBETerm = FStar.TypeChecker.NBETerm
module NBET    = FStar.TypeChecker.NBETerm
open FStar.Tactics.Native
open FStar.Tactics.InterpFuns

let tacdbg = BU.mk_ref false

// IN F*: let rec e_tactic_0 (#r:Type) (er : embedding r) : embedding (tac r)
let rec e_tactic_0 (er : embedding<'r>) : embedding<tac<'r>> // JUST FSHARP
    =
    mk_emb (fun _ _ _ -> failwith "Impossible: embedding tactic (0)?")
           (fun t w norm -> Some <| unembed_tactic_0 er t norm)
           (FStar.Syntax.Embeddings.term_as_fv S.t_unit)

// IN F*: and e_tactic_1 (#a:Type) (#r:Type) (ea : embedding a) (er : embedding r) : embedding (a -> tac r)
and e_tactic_1 (ea : embedding<'a>) (er : embedding<'r>) : embedding<('a -> tac<'r>)> // JUST FSHARP
    =
    mk_emb (fun _ _ _ -> failwith "Impossible: embedding tactic (1)?")
           (fun t w -> unembed_tactic_1 ea er t)
           (FStar.Syntax.Embeddings.term_as_fv S.t_unit)

// IN F*: and e_tactic_nbe_0 (#r:Type) (er : NBET.embedding r) : NBET.embedding (tac r)
and e_tactic_nbe_0 (er : NBET.embedding<'r>) : NBET.embedding<tac<'r>> // JUST FSHARP
    =
    NBETerm.mk_emb
           (fun _ -> failwith "Impossible: NBE embedding tactic (0)?")
           (fun t -> Some <| unembed_tactic_nbe_0 er t)
           (NBET.Constant NBET.Unit)

// IN F*: and e_tactic_nbe_1 (#a:Type) (#r:Type) (ea : NBET.embedding a) (er : NBET.embedding r) : NBET.embedding (a -> tac r)
and e_tactic_nbe_1 (ea : NBET.embedding<'a>) (er : NBET.embedding<'r>) : NBET.embedding<('a -> tac<'r>)> // JUST FSHARP
    =
    NBETerm.mk_emb
           (fun _ -> failwith "Impossible: NBE embedding tactic (1)?")
           (fun t -> unembed_tactic_nbe_1 ea er t)
           (NBET.Constant NBET.Unit)

and primitive_steps () : list<Cfg.primitive_step> =
    (* NB: We need a PRECISE number for the universe arguments or NBE will
     * just go crazy. Most of the tactics work on ground types and thus have 0
     * universe arguments. Those polymorphic, usually take 1 universe per Type argument. *)

    (* mktot1/mktot2 uses names in FStar.Tactics.Builtins, we override these few who
     * are in other modules: *)
    let tracepoint =
      { mktot1 0 "tracepoint" tracepoint E.e_proofstate e_unit
                              tracepoint E.e_proofstate_nbe NBET.e_unit
        with Cfg.name = Ident.lid_of_str "FStar.Tactics.Types.tracepoint" }
    in
    let set_proofstate_range =
      { mktot2 0 "set_proofstate_range" set_proofstate_range E.e_proofstate e_range E.e_proofstate
                                        set_proofstate_range E.e_proofstate_nbe NBET.e_range E.e_proofstate_nbe
        with Cfg.name = Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range" }
    in
    let incr_depth =
      { mktot1 0 "incr_depth" incr_depth E.e_proofstate E.e_proofstate
                              incr_depth E.e_proofstate_nbe E.e_proofstate_nbe
        with Cfg.name = Ident.lid_of_str "FStar.Tactics.Types.incr_depth" }
    in
    let decr_depth =
      { mktot1 0 "decr_depth" decr_depth E.e_proofstate E.e_proofstate
                              decr_depth E.e_proofstate_nbe E.e_proofstate_nbe
        with Cfg.name = Ident.lid_of_str "FStar.Tactics.Types.decr_depth" }
    in
    (* Sigh, due to lack to expressive typing we need to duplicate a bunch of information here,
     * like which embeddings are needed for the arguments, but more annoyingly the underlying
     * implementation. Would be nice to have something better in the not-so-long run. *)
    [
      incr_depth;
      decr_depth;
      tracepoint;
      set_proofstate_range;
      mktot2 0 "push_binder"   (fun env b -> Env.push_binders env [b]) RE.e_env RE.e_binder RE.e_env
                               (fun env b -> Env.push_binders env [b]) NRE.e_env NRE.e_binder NRE.e_env;

      //nb: the e_any embedding is never used
      mktac2 1 "fail"          (fun _ -> fail) e_any e_string e_any
                               (fun _ -> fail) NBET.e_any NBET.e_string NBET.e_any;

      mktac1 0 "trivial"       trivial e_unit e_unit
                               trivial NBET.e_unit NBET.e_unit;

      mktac2 1 "__trytac"      (fun _ -> trytac) e_any (e_tactic_0 e_any) (e_option e_any)
                               (fun _ -> trytac) NBET.e_any (e_tactic_nbe_0 NBET.e_any) (NBET.e_option NBET.e_any);

      mktac1 0 "intro"         intro e_unit RE.e_binder
                               intro NBET.e_unit NRE.e_binder;

      mktac1 0 "intro_rec"     intro_rec e_unit (e_tuple2 RE.e_binder RE.e_binder)
                               intro_rec NBET.e_unit (NBET.e_tuple2 NRE.e_binder NRE.e_binder);

      mktac1 0 "norm"          norm (e_list e_norm_step) e_unit
                               norm (NBET.e_list NBET.e_norm_step) NBET.e_unit;

      mktac3 0 "norm_term_env" norm_term_env RE.e_env (e_list e_norm_step) RE.e_term RE.e_term
                               norm_term_env NRE.e_env (NBET.e_list NBET.e_norm_step) NRE.e_term NRE.e_term;

      mktac2 0 "norm_binder_type"
                               norm_binder_type (e_list e_norm_step) RE.e_binder e_unit
                               norm_binder_type (NBET.e_list NBET.e_norm_step) NRE.e_binder NBET.e_unit;

      mktac2 0 "rename_to"     rename_to RE.e_binder e_string e_unit
                               rename_to NRE.e_binder NBET.e_string NBET.e_unit;

      mktac1 0 "binder_retype" binder_retype RE.e_binder e_unit
                               binder_retype NRE.e_binder NBET.e_unit;

      mktac1 0 "revert"        revert e_unit e_unit
                               revert NBET.e_unit NBET.e_unit;

      mktac1 0 "clear_top"     clear_top e_unit e_unit
                               clear_top NBET.e_unit NBET.e_unit;

      mktac1 0 "clear"         clear RE.e_binder e_unit
                               clear NRE.e_binder NBET.e_unit;

      mktac1 0 "rewrite"       rewrite RE.e_binder e_unit
                               rewrite NRE.e_binder NBET.e_unit;

      mktac1 0 "smt"           smt e_unit e_unit
                               smt NBET.e_unit NBET.e_unit;

      mktac1 0 "refine_intro"  refine_intro e_unit e_unit
                               refine_intro NBET.e_unit NBET.e_unit;

      mktac2 0 "t_exact"       t_exact e_bool RE.e_term e_unit
                               t_exact NBET.e_bool NRE.e_term NBET.e_unit;

      mktac1 0 "apply"         (apply  true) RE.e_term e_unit
                               (apply  true) NRE.e_term NBET.e_unit;

      mktac1 0 "apply_raw"     (apply false) RE.e_term e_unit
                               (apply false) NRE.e_term NBET.e_unit;

      mktac1 0 "apply_lemma"   apply_lemma RE.e_term e_unit
                               apply_lemma NRE.e_term NBET.e_unit;

      mktac5 2 "__divide"      (fun _ _ -> divide) e_any e_any e_int (e_tactic_0 e_any) (e_tactic_0 e_any) (e_tuple2 e_any e_any)
                               (fun _ _ -> divide) NBET.e_any NBET.e_any NBET.e_int (e_tactic_nbe_0 NBET.e_any) (e_tactic_nbe_0 NBET.e_any) (NBET.e_tuple2 NBET.e_any NBET.e_any);

      mktac2 0 "__seq"         seq (e_tactic_0 e_unit) (e_tactic_0 e_unit) e_unit
                               seq (e_tactic_nbe_0 NBET.e_unit) (e_tactic_nbe_0 NBET.e_unit) NBET.e_unit;

      mktac1 0 "set_options"   set_options e_string e_unit
                               set_options NBET.e_string NBET.e_unit;

      mktac1 0 "tc"            tc RE.e_term RE.e_term
                               tc NRE.e_term NRE.e_term;

      mktac1 0 "unshelve"      unshelve RE.e_term e_unit
                               unshelve NRE.e_term NBET.e_unit;

      mktac2 1 "unquote"       unquote e_any RE.e_term e_any
                               (fun _ _ -> failwith "NBE unquote") NBET.e_any NRE.e_term NBET.e_any;

      mktac1 0 "prune"         prune e_string e_unit
                               prune NBET.e_string NBET.e_unit;

      mktac1 0 "addns"         addns e_string e_unit
                               addns NBET.e_string NBET.e_unit;

      mktac1 0 "print"         print e_string e_unit
                               print NBET.e_string NBET.e_unit;

      mktac1 0 "debug"         debug e_string e_unit
                               debug NBET.e_string NBET.e_unit;

      mktac1 0 "dump"          print_proof_state e_string e_unit
                               print_proof_state NBET.e_string NBET.e_unit;

      mktac1 0 "dump1"         print_proof_state1 e_string e_unit
                               print_proof_state1 NBET.e_string NBET.e_unit;

      mktac2 0 "__pointwise"   pointwise E.e_direction (e_tactic_0 e_unit) e_unit
                               pointwise E.e_direction_nbe (e_tactic_nbe_0 NBET.e_unit) NBET.e_unit;

      mktac2 0 "__topdown_rewrite" topdown_rewrite (e_tactic_1 RE.e_term (e_tuple2 e_bool e_int)) (e_tactic_0 e_unit) e_unit
                                   topdown_rewrite (e_tactic_nbe_1 NRE.e_term (NBET.e_tuple2 NBET.e_bool NBET.e_int)) (e_tactic_nbe_0 NBET.e_unit) NBET.e_unit;

      mktac1 0 "trefl"         trefl   e_unit e_unit
                               trefl   NBET.e_unit NBET.e_unit;

      mktac1 0 "later"         later   e_unit e_unit
                               later   NBET.e_unit NBET.e_unit;

      mktac1 0 "dup"           dup     e_unit e_unit
                               dup     NBET.e_unit NBET.e_unit;

      mktac1 0 "flip"          flip    e_unit e_unit
                               flip    NBET.e_unit NBET.e_unit;

      mktac1 0 "qed"           qed     e_unit e_unit
                               qed     NBET.e_unit NBET.e_unit;

      mktac1 0 "dismiss"       dismiss e_unit e_unit
                               dismiss NBET.e_unit NBET.e_unit;

      mktac1 0 "tadmit"        tadmit  e_unit e_unit
                               tadmit  NBET.e_unit NBET.e_unit;

      mktac1 0 "cases"         cases RE.e_term (e_tuple2 RE.e_term RE.e_term)
                               cases NRE.e_term (NBET.e_tuple2 NRE.e_term NRE.e_term);

      mktac1 0 "t_destruct"    t_destruct RE.e_term (e_list (e_tuple2 RE.e_fv e_int))
                               t_destruct NRE.e_term (NBET.e_list (NBET.e_tuple2 NRE.e_fv NBET.e_int));

      mktac1 0 "top_env"       top_env     e_unit RE.e_env
                               top_env     NBET.e_unit NRE.e_env;

      mktac1 0 "cur_env"       cur_env     e_unit RE.e_env
                               cur_env     NBET.e_unit NRE.e_env;

      mktac1 0 "cur_goal"      cur_goal'   e_unit RE.e_term
                               cur_goal'   NBET.e_unit NRE.e_term;

      mktac1 0 "cur_witness"   cur_witness e_unit RE.e_term
                               cur_witness NBET.e_unit NRE.e_term;

      mktac1 0 "inspect"       inspect RE.e_term      RE.e_term_view
                               inspect NRE.e_term     NRE.e_term_view;

      mktac1 0 "pack"          pack    RE.e_term_view RE.e_term
                               pack    NRE.e_term_view NRE.e_term;

      mktac1 0 "fresh"         fresh       e_unit e_int
                               fresh       NBET.e_unit NBET.e_int;

      mktac1 0 "ngoals"        ngoals      e_unit e_int
                               ngoals      NBET.e_unit NBET.e_int;

      mktac1 0 "ngoals_smt"    ngoals_smt  e_unit e_int
                               ngoals_smt  NBET.e_unit NBET.e_int;

      mktac1 0 "is_guard"      is_guard    e_unit e_bool
                               is_guard    NBET.e_unit NBET.e_bool;

      mktac2 0 "uvar_env"      uvar_env RE.e_env (e_option RE.e_term) RE.e_term
                               uvar_env NRE.e_env (NBET.e_option NRE.e_term) NRE.e_term;

      mktac3 0 "unify_env"     unify_env RE.e_env RE.e_term RE.e_term e_bool
                               unify_env NRE.e_env NRE.e_term NRE.e_term NBET.e_bool;

      mktac3 0 "launch_process" launch_process e_string (e_list e_string) e_string e_string
                                launch_process NBET.e_string (NBET.e_list NBET.e_string) NBET.e_string NBET.e_string;

      mktac2 0 "fresh_bv_named"  fresh_bv_named e_string RE.e_term RE.e_bv
                                 fresh_bv_named NBET.e_string NRE.e_term NRE.e_bv;

      mktac1 0 "change"          change RE.e_term e_unit
                                 change NRE.e_term NBET.e_unit;

      mktac1 0 "get_guard_policy" get_guard_policy e_unit E.e_guard_policy
                                  get_guard_policy NBET.e_unit E.e_guard_policy_nbe;

      mktac1 0 "set_guard_policy" set_guard_policy E.e_guard_policy e_unit
                                  set_guard_policy E.e_guard_policy_nbe NBET.e_unit;

      mktac1 0 "lax_on"           lax_on e_unit e_bool
                                  lax_on NBET.e_unit NBET.e_bool;

    ] @ reflection_primops @ native_tactics_steps

// Please note, these markers are for some makefile magic that tweaks this function in the OCaml output

//IN F*: and unembed_tactic_1 (#a:Type) (#r:Type) (ea:embedding a) (er:embedding r) (f:term) (ncb:norm_cb) : option (a -> tac r) =
and unembed_tactic_1<'a,'r> (ea:embedding<'a>) (er:embedding<'r>) (f:term) (ncb:norm_cb) : option<('a -> tac<'r>)> = //JUST FSHARP
    Some (fun x ->
      let rng = FStar.Range.dummyRange  in
      let x_tm = embed ea rng x ncb in
      let app = S.mk_Tm_app f [as_arg x_tm] None rng in
      unembed_tactic_0 er app ncb)

//IN F*: and unembed_tactic_0 (#b:Type) (eb:embedding b) (embedded_tac_b:term) (ncb:norm_cb) : tac b =
and unembed_tactic_0<'b> (eb:embedding<'b>) (embedded_tac_b:term) (ncb:norm_cb) : tac<'b> = //JUST FSHARP
    bind get (fun proof_state ->
    let rng = embedded_tac_b.pos in
    let tm = S.mk_Tm_app embedded_tac_b
                         [S.as_arg (embed E.e_proofstate rng proof_state ncb)]
                          None
                          rng in

    // Why not HNF? While we don't care about strong reduction we need more than head
    // normal form due to primitive steps. Consider `norm (steps 2)`: we need to normalize
    // `steps 2` before caling norm, or it will fail to unembed the set of steps. Further,
    // at this moment at least, the normalizer will not call into any step of arity > 1.
    let steps = [Env.Weak; Env.Reify; Env.UnfoldUntil delta_constant; Env.UnfoldTac; Env.Primops; Env.Unascribe] in

    // Maybe use NBE if the user asked for it
    let norm_f = if Options.tactics_nbe ()
                 then NBE.normalize
                 else N.normalize_with_primitive_steps
    in
    if proof_state.tac_verb_dbg then
        BU.print1 "Starting normalizer with %s\n" (Print.term_to_string tm);
    let result = norm_f (primitive_steps ()) steps proof_state.main_context tm in
    if proof_state.tac_verb_dbg then
        BU.print1 "Reduced tactic: got %s\n" (Print.term_to_string result);

    // F* requires more annotations.
    // IN F*: let res : option<__result<b>> = unembed (E.e_result eb) result ncb in
    let res = unembed (E.e_result eb) result ncb in //JUST FSHARP

    match res with
    | Some (Success (b, ps)) ->
        bind (set ps) (fun _ -> ret b)

    | Some (Failed (msg, ps)) ->
        bind (set ps) (fun _ -> fail msg)

    | None ->
        Err.raise_error (Err.Fatal_TacticGotStuck, (BU.format1 "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s" (Print.term_to_string result))) proof_state.main_context.range
    )

//IN F*: and unembed_tactic_nbe_1 (#a:Type) (#r:Type) (ea:NBET.embedding a) (er:NBET.embedding r) (f:NBET.t) : option (a -> tac r) =
and unembed_tactic_nbe_1<'a,'r> (ea:NBET.embedding<'a>) (er:NBET.embedding<'r>) (f:NBET.t) : option<('a -> tac<'r>)> = //JUST FSHARP
    Some (fun x ->
      let x_tm = NBET.embed ea x in
      let app = NBE.iapp f [NBET.as_arg x_tm] in
      unembed_tactic_nbe_0 er app)

//IN F*: and unembed_tactic_nbe_0 (#b:Type) (eb:NBET.embedding b) (embedded_tac_b:NBET.t) : tac b =
and unembed_tactic_nbe_0<'b> (eb:NBET.embedding<'b>) (embedded_tac_b:NBET.t) : tac<'b> = //JUST FSHARP
    bind get (fun proof_state ->

    (* Applying is normalizing!!! *)
    let result = NBE.iapp embedded_tac_b [NBET.as_arg (NBET.embed E.e_proofstate_nbe proof_state)] in

    // F* requires more annotations.
    // IN F*: let res : option<__result<b>> = NBET.unembed (E.e_result_nbe eb) result in
    let res = NBET.unembed (E.e_result_nbe eb) result in //JUST FSHARP

    match res with
    | Some (Success (b, ps)) ->
        bind (set ps) (fun _ -> ret b)

    | Some (Failed (msg, ps)) ->
        bind (set ps) (fun _ -> fail msg)

    | None ->
        Err.raise_error (Err.Fatal_TacticGotStuck, (BU.format1 "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s" (NBET.t_to_string result))) proof_state.main_context.range
    )

let report_implicits ps (is : Env.implicits) : unit =
    let errs = List.map (fun imp ->
                (Err.Error_UninstantiatedUnificationVarInTactic, BU.format3 ("Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")")
                             (Print.uvar_to_string imp.imp_uvar.ctx_uvar_head)
                             (Print.term_to_string imp.imp_uvar.ctx_uvar_typ)
                             imp.imp_reason,
                 imp.imp_range)) is in
    Err.add_errors errs

let run_tactic_on_typ
        (rng_tac : Range.range) (rng_goal : Range.range)
        (tactic:term) (env:env) (typ:typ)
                    : list<goal> // remaining goals
                    * term // witness
                    =
    if !tacdbg then
        BU.print1 "Typechecking tactic: (%s) {\n" (Print.term_to_string tactic);

    (* Do NOT use the returned tactic, the typechecker is not idempotent and
     * will mess up the monadic lifts. We're just making sure it's well-typed
     * so it won't get stuck. c.f #1307 *)
    let _, _, g = TcTerm.tc_reified_tactic env tactic in
    if !tacdbg then
        BU.print_string "}\n";

    TcRel.force_trivial_guard env g;
    Err.stop_if_err ();
    let tau = unembed_tactic_0 e_unit tactic FStar.Syntax.Embeddings.id_norm_cb in
    let env, _ = Env.clear_expected_typ env in
    let env = { env with Env.instantiate_imp = false } in
    (* TODO: We do not faithfully expose universes to metaprograms *)
    let env = { env with Env.lax_universes = true } in
    let env = { env with failhard = true } in
    let rng = range_of_rng (use_range rng_goal) (use_range rng_tac) in
    let ps, w = proofstate_of_goal_ty rng env typ in

    Reflection.Basic.env_hook := Some env;
    if !tacdbg then
        BU.print1 "Running tactic with goal = (%s) {\n" (Print.term_to_string typ);
    let res, ms = BU.record_time (fun () -> run_safe tau ps) in
    if !tacdbg then
        BU.print3 "}\nTactic %s ran in %s ms (%s)\n" (Print.term_to_string tactic) (string_of_int ms) (Print.lid_to_string env.curmodule);
    match res with
    | Success (_, ps) ->
        if !tacdbg then
            BU.print1 "Tactic generated proofterm %s\n" (Print.term_to_string w);
        List.iter (fun g -> if is_irrelevant g
                            then if TcRel.teq_nosmt (goal_env g) (goal_witness g) U.exp_unit
                                 then ()
                                 else failwith (BU.format1 "Irrelevant tactic witness does not unify with (): %s"
                                                    (Print.term_to_string (goal_witness g)))
                            else ())
                  (ps.goals @ ps.smt_goals);

        // Check that all implicits were instantiated
        if !tacdbg then
            BU.print1 "About to check tactic implicits: %s\n" (FStar.Common.string_of_list
                                                                    (fun imp -> Print.ctx_uvar_to_string imp.imp_uvar)
                                                                    ps.all_implicits);
        let g = {Env.trivial_guard with Env.implicits=ps.all_implicits} in
        let g = TcRel.solve_deferred_constraints env g in
        if !tacdbg then
            BU.print2 "Checked %s implicits (1): %s\n"
                        (string_of_int (List.length ps.all_implicits))
                        (FStar.Common.string_of_list
                                (fun imp -> Print.ctx_uvar_to_string imp.imp_uvar)
                                ps.all_implicits);
        let g = TcRel.resolve_implicits_tac env g in
        if !tacdbg then
            BU.print2 "Checked %s implicits (2): %s\n"
                        (string_of_int (List.length ps.all_implicits))
                        (FStar.Common.string_of_list
                                (fun imp -> Print.ctx_uvar_to_string imp.imp_uvar)
                                ps.all_implicits);
        report_implicits ps g.implicits;
        // /implicits

        if !tacdbg then
            dump_proofstate (subst_proof_state (Cfg.psc_subst ps.psc) ps) "at the finish line";
        (ps.goals@ps.smt_goals, w)

    | Failed (s, ps) ->
        dump_proofstate (subst_proof_state (Cfg.psc_subst ps.psc) ps) "at the time of failure";
        Err.raise_error (Err.Fatal_UserTacticFailure, (BU.format1 "user tactic failed: %s" s)) ps.entry_range

// Polarity
type pol =
    | Pos
    | Neg
    | Both // traversing both polarities at once

// Result of traversal
type tres_m<'a> =
    | Unchanged of 'a
    | Simplified of 'a * list<goal>
    | Dual of 'a * 'a * list<goal>

type tres = tres_m<term>

let tpure x = Unchanged x

let flip p = match p with
    | Pos -> Neg
    | Neg -> Pos
    | Both -> Both

let by_tactic_interp (pol:pol) (e:Env.env) (t:term) : tres =
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with

    // by_tactic marker
    | Tm_fvar fv, [(rett, Some (Implicit _)); (tactic, None); (assertion, None)]
            when S.fv_eq_lid fv PC.by_tactic_lid ->
        begin match pol with
        | Pos ->
            let gs, _ = run_tactic_on_typ tactic.pos assertion.pos tactic e assertion in
            Simplified (FStar.Syntax.Util.t_true, gs)

        | Both ->
            let gs, _ = run_tactic_on_typ tactic.pos assertion.pos tactic e assertion in
            Dual (assertion, FStar.Syntax.Util.t_true, gs)

        | Neg ->
            // Peel away tactics in negative positions, they're assumptions!
            Simplified (assertion, [])
        end

    // spinoff marker: simply spin off a query independently.
    // So, equivalent to `by_tactic idtac` without importing the (somewhat heavy) tactics module
    | Tm_fvar fv, [(assertion, None)]
            when S.fv_eq_lid fv PC.spinoff_lid ->
        begin  match pol with
        | Pos ->
            Simplified (FStar.Syntax.Util.t_true, [fst <| goal_of_goal_ty e assertion])

        | Both ->
            Dual (assertion, FStar.Syntax.Util.t_true, [fst <| goal_of_goal_ty e assertion])

        | Neg ->
            Simplified (assertion, [])
        end

    | _ ->
        Unchanged t

let explode (t : tres_m<'a>) : 'a * 'a * list<goal> =
    match t with
    | Unchanged t -> (t, t, [])
    | Simplified (t, gs) -> (t, t, gs)
    | Dual (tn, tp, gs) -> (tn, tp, gs)

let comb1 (f : 'a -> 'b) : tres_m<'a> -> tres_m<'b> = function
    | Unchanged t -> Unchanged (f t)
    | Simplified (t, gs) -> Simplified (f t, gs)
    | Dual (tn, tp, gs) -> Dual (f tn, f tp, gs)

let comb2 (f : 'a -> 'b -> 'c ) (x : tres_m<'a>) (y : tres_m<'b>) : tres_m<'c> =
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

let comb_list (rs : list<tres_m<'a>>) : tres_m<list<'a>> =
    let rec aux rs acc =
        match rs with
        | [] -> acc
        | hd::tl -> aux tl (comb2 (fun l r -> l::r) hd acc)
    in
    aux (List.rev rs) (tpure [])

let emit (gs : list<goal>) (m : tres_m<'a>) : tres_m<'a> =
    comb2 (fun () x -> x) (Simplified ((), gs)) m

let rec traverse (f: pol -> Env.env -> term -> tres) (pol:pol) (e:Env.env) (t:term) : tres =
    let r =
        match (SS.compress t).n with
        | Tm_uinst (t,us) -> let tr = traverse f pol e t in
                             comb1 (fun t' -> Tm_uinst (t', us)) tr

        | Tm_meta (t, m) -> let tr = traverse f pol e t in
                            comb1 (fun t' -> Tm_meta (t', m)) tr

        | Tm_app ({ n = Tm_fvar fv }, [(p,_); (q,_)]) when S.fv_eq_lid fv PC.imp_lid ->
               // ==> is specialized to U_zero
               let x = S.new_bv None (U.mk_squash U_zero p) in
               let r1 = traverse f (flip pol)  e                p in
               let r2 = traverse f       pol  (Env.push_bv e x) q in
               comb2 (fun l r -> (U.mk_imp l r).n) r1 r2

        (* p <==> q is special, each side is bipolar *)
        (* So we traverse its arguments with pol = Both, and negative and positive versions *)
        (* of p and q *)
        (* then we return (in general) (p- ==> q+) /\ (q- ==> p+) *)
        (* But if neither side ran tactics, we just keep p <==> q *)
        | Tm_app ({ n = Tm_fvar fv }, [(p,_); (q,_)]) when S.fv_eq_lid fv PC.iff_lid ->
               // <==> is specialized to U_zero
               let xp = S.new_bv None (U.mk_squash U_zero p) in
               let xq = S.new_bv None (U.mk_squash U_zero q) in
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

        | Tm_app (hd, args) ->
                let r0 = traverse f pol e hd in
                let r1 = List.fold_right (fun (a, q) r ->
                                              let r' = traverse f pol e a in
                                              comb2 (fun a args -> (a, q)::args) r' r)
                                                 args (tpure []) in
                comb2 (fun hd args -> Tm_app (hd, args)) r0 r1

        | Tm_abs (bs, t, k) ->
                // TODO: traverse k?
                let bs, topen = SS.open_term bs t in
                let e' = Env.push_binders e bs in
                let r0 = List.map (fun (bv, aq) ->
                                     let r = traverse f (flip pol) e bv.sort in
                                     comb1 (fun s' -> ({ bv with sort = s' }, aq)) r
                                  ) bs
                in
                let rbs = comb_list r0 in
                let rt = traverse f pol e' topen in
                comb2 (fun bs t -> (U.abs bs t k).n) rbs rt

        | Tm_ascribed (t, asc, ef) ->
            // TODO: traverse the types?
            comb1 (fun t -> Tm_ascribed (t, asc, ef)) (traverse f pol e t)

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

let getprop (e:env) (t:term) : option<term> =
    let tn = N.normalize [Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant] e t in
    U.un_squash tn

let preprocess (env:Env.env) (goal:term) : list<(Env.env * term * FStar.Options.optionstate)> =
    tacdbg := Env.debug env (Options.Other "Tac");
    if !tacdbg then
        BU.print2 "About to preprocess %s |= %s\n"
                        (Env.all_binders env |> Print.binders_to_string ",")
                        (Print.term_to_string goal);
    let initial = (1, []) in
    // This match should never fail
    let (t', gs) =
        match traverse by_tactic_interp Pos env goal with
        | Unchanged t' -> (t', [])
        | Simplified (t', gs) -> (t', gs)
        | _ -> failwith "no"
    in
    if !tacdbg then
        BU.print2 "Main goal simplified to: %s |- %s\n"
                (Env.all_binders env |> Print.binders_to_string ", ")
                (Print.term_to_string t');
    let s = initial in
    let s = List.fold_left (fun (n,gs) g ->
                 let phi = match getprop (goal_env g) (goal_type g) with
                           | None ->
                                Err.raise_error (Err.Fatal_TacticProofRelevantGoal,
                                    (BU.format1 "Tactic returned proof-relevant goal: %s" (Print.term_to_string (goal_type g)))) env.range
                           | Some phi -> phi
                 in
                 if !tacdbg then
                     BU.print2 "Got goal #%s: %s\n" (string_of_int n) (Print.term_to_string (goal_type g));
                 let gt' = TcUtil.label ("Could not prove goal #" ^ string_of_int n) goal.pos phi in
                 (n+1, (goal_env g, gt', g.opts)::gs)) s gs in
    let (_, gs) = s in
    // Use default opts for main goal
    (env, t', FStar.Options.peek ()) :: gs

let reify_tactic (a : term) : term =
    let r = S.mk_Tm_uinst (S.fv_to_tm (S.lid_as_fv PC.reify_tactic_lid delta_equational None)) [U_zero] in
    mk_Tm_app r [S.iarg t_unit; S.as_arg a] None a.pos

let synthesize (env:Env.env) (typ:typ) (tau:term) : term =
    // Don't run the tactic (and end with a magic) when nosynth is set, cf. issue #73 in fstar-mode.el
    if env.nosynth
    then mk_Tm_app (TcUtil.fvar_const env PC.magic_lid) [S.as_arg U.exp_unit] None typ.pos
    else begin
    tacdbg := Env.debug env (Options.Other "Tac");

    let gs, w = run_tactic_on_typ tau.pos typ.pos (reify_tactic tau) env typ in
    // Check that all goals left are irrelevant and provable
    // TODO: It would be nicer to combine all of these into a guard and return
    // that to TcTerm, but the varying environments make it awkward.
    List.iter (fun g ->
        match getprop (goal_env g) (goal_type g) with
        | Some vc ->
            begin
            if !tacdbg then
              BU.print1 "Synthesis left a goal: %s\n" (Print.term_to_string vc);
            let guard = { guard_f = FStar.TypeChecker.Common.NonTrivial vc
                        ; deferred = []
                        ; univ_ineqs = [], []
                        ; implicits = [] } in
            TcRel.force_trivial_guard (goal_env g) guard
            end
        | None ->
            Err.raise_error (Err.Fatal_OpenGoalsInSynthesis, "synthesis left open goals") typ.pos) gs;
    w
    end

let splice (env:Env.env) (tau:term) : list<sigelt> =
    if env.nosynth then [] else begin
    tacdbg := Env.debug env (Options.Other "Tac");
    let typ = S.t_decls in // running with goal type FStar.Reflection.Data.decls
    let gs, w = run_tactic_on_typ tau.pos tau.pos (reify_tactic tau) env typ in
    // Check that all goals left are irrelevant. We don't need to check their
    // validity, as we will typecheck the witness independently.
    // TODO: Do not retypecheck and do just like `synth`
    if List.existsML (fun g -> not (Option.isSome (getprop (goal_env g) (goal_type g)))) gs
        then Err.raise_error (Err.Fatal_OpenGoalsInSynthesis, "splice left open goals") typ.pos;

    // Fully normalize the witness
    let w = N.normalize [Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant;
                         Env.Primops; Env.Unascribe; Env.Unmeta] env w in

    if !tacdbg then
      BU.print1 "splice: got witness = %s\n" (Print.term_to_string w);

    // Unembed the result, this must work if things are well-typed
    match unembed (e_list RE.e_sigelt) w FStar.Syntax.Embeddings.id_norm_cb with
    | Some sigelts -> sigelts
    | None -> Err.raise_error (Err.Fatal_SpliceUnembedFail, "splice: failed to unembed sigelts") typ.pos
    end
