#light "off"
module FStar.Tactics.Interpreter
open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util

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
type name = bv

let remove_unit (f: 'a -> unit -> 'b) (x:'a) : 'b = f x ()

let mk_pure_interpretation_1 (f:'a -> 'b) (unembed_a:term -> 'a) (embed_b:'b -> term) (args:args) =
    match args with
    | [a] -> embed_b (f (unembed_a (fst a)))
    | _ -> failwith "Unexpected interpretation of pure primitive"

let mk_tactic_interpretation_0 (ps:proofstate) (t:tac<'a>) (embed_a:'a -> term) (t_a:typ) (args:args) : term =
 (*  We have: t () embedded_state
     The idea is to:
        1. unembed the state
        2. run the `t` tactic
        3. embed the result and final state and return it to the normalizer
  *)
  match args with
  | [_unit; (embedded_state, _)] ->
    printfn "Reached forall_intro_interpretation, goals are: %s" (Print.term_to_string embedded_state);
    let goals, smt_goals = E.unembed_state ps.main_context embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run t ps in
    E.embed_result res embed_a t_a
  | _ ->
    failwith ("Unexpected application of tactic primitive")

let mk_tactic_interpretation_1 (ps:proofstate)
                               (t:'b -> tac<'a>) (unembed_b:term -> 'b)
                               (embed_a:'a -> term) (t_a:typ) (args:args) : term =
  match args with
  | [(b, _); (embedded_state, _)] ->
    printfn "Reached forall_intro_interpretation, goals are: %s" (Print.term_to_string embedded_state);
    let goals, smt_goals = E.unembed_state ps.main_context embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run (t (unembed_b b)) ps in
    E.embed_result res embed_a t_a
  | _ ->
    failwith ("Unexpected application of tactic primitive")

let rec primitive_steps ps : list<N.primitive_step> =
    [{N.name=E.fstar_tactics_lid "forall_intros";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_0 ps intros E.embed_binders E.fstar_tactics_binders};

     {N.name=E.fstar_tactics_lid "implies_intro";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_0 ps imp_intro E.embed_binder E.fstar_tactics_binder};

     {N.name=E.fstar_tactics_lid "revert";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_0 ps revert E.embed_unit FStar.TypeChecker.Common.t_unit};

     {N.name=E.fstar_tactics_lid "clear";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_0 ps clear E.embed_unit FStar.TypeChecker.Common.t_unit};

     {N.name=E.fstar_tactics_lid "split";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_0 ps split E.embed_unit FStar.TypeChecker.Common.t_unit};

     {N.name=E.fstar_tactics_lid "merge";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_0 ps merge_sub_goals E.embed_unit FStar.TypeChecker.Common.t_unit};

     {N.name=E.fstar_tactics_lid "rewrite";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_1 ps rewrite E.unembed_binder E.embed_unit FStar.TypeChecker.Common.t_unit};

     {N.name=E.fstar_tactics_lid "smt";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_0 ps smt E.embed_unit FStar.TypeChecker.Common.t_unit};

     {N.name=E.fstar_tactics_lid "visit";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_1 ps visit
                                (remove_unit (unembed_tactic E.embed_unit E.unembed_unit))
                                E.embed_unit
                                FStar.TypeChecker.Common.t_unit};

     {N.name=E.fstar_tactics_lid "focus";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation_1 ps (focus_cur_goal "user_tactic")
                                (remove_unit (unembed_tactic E.embed_unit E.unembed_unit))
                                E.embed_unit
                                FStar.TypeChecker.Common.t_unit};

     {N.name=E.fstar_tactics_lid "term_as_formula";
      N.arity=1;
      N.interpretation=mk_pure_interpretation_1 U.destruct_typ_as_formula E.unembed_term (E.embed_option E.embed_formula E.fstar_tactics_formula)};
    ]



and unembed_tactic<'a,'b> (embed_a:'a -> term) (unembed_b:term -> 'b) (embedded_a_tac_b:term) (a:'a) : tac<'b> =
    bind get (fun proof_state ->
    let tm = S.mk_Tm_app (U.mk_reify (S.mk_Tm_app embedded_a_tac_b [S.as_arg (embed_a a)] None Range.dummyRange))
                            [S.as_arg (E.embed_state (proof_state.goals, []))]
                            None
                            Range.dummyRange in
    let steps = [N.Reify; N.Beta; N.UnfoldUntil Delta_constant; N.Zeta; N.Iota; N.Primops] in
                 printfn "Starting normalizer with %s" (Print.term_to_string tm);
                 Options.set_option "debug_level" (Options.List [Options.String "Norm"]);
    let result = N.normalize_with_primitive_steps (primitive_steps proof_state) steps proof_state.main_context tm in
            Options.set_option "debug_level" (Options.List []);
            printfn "Reduced tactic: got %s" (Print.term_to_string result);
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
        fail msg))))


let evaluate_user_tactic : tac<unit>
    = with_cur_goal "evaluate_user_tactic" (fun goal ->
      bind get (fun proof_state ->
          let hd, args = U.head_and_args goal.goal_ty in
          match (U.un_uinst hd).n, args with
          | Tm_fvar fv, [(tactic, _); (assertion, _)]
                when S.fv_eq_lid fv E.by_tactic_lid ->
            focus_cur_goal "user tactic"
            (bind (replace ({goal with goal_ty=assertion})) (fun _ ->
                   unembed_tactic E.embed_unit E.unembed_unit tactic ()))
          | _ ->
            fail "Not a user tactic"))



let preprocess (env:Env.env) (goal:term) : list<(Env.env * term)> =
    if Ident.lid_equals
            (Env.current_module env)
            FStar.Syntax.Const.prims_lid
    || BU.starts_with (Ident.string_of_lid (Env.current_module env)) "FStar."
    then [env, goal]
    else let _ = printfn "About to preprocess %s\n" (Print.term_to_string goal) in
         let p = proofstate_of_goal_ty env goal in
         match run (visit evaluate_user_tactic) p with
         | Success (_, p2) ->
           (p2.goals @ p2.smt_goals) |> List.map (fun g ->
             printfn "Got goal: %s" (goal_to_string g);
             g.context, g.goal_ty)
         | Failed (msg, _) ->
           printfn "Tactic failed: %s" msg;
           printfn "Got goal: %s" (goal_to_string ({context=env; witness=None; goal_ty=goal}));
           [env, goal]
