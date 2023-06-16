open Prims
type ('g, 't) vprop_typing = unit
type preamble =
  {
  g0: Pulse_Typing_Env.env ;
  ctxt: Pulse_Syntax_Base.vprop ;
  ctxt_typing: unit ;
  t: Pulse_Syntax_Base.st_term ;
  c: Pulse_Syntax_Base.comp_st ;
  uvs: Pulse_Typing_Env.env }
let (__proj__Mkpreamble__item__g0 : preamble -> Pulse_Typing_Env.env) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; t; c; uvs;_} -> g0
let (__proj__Mkpreamble__item__ctxt : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; t; c; uvs;_} -> ctxt

let (__proj__Mkpreamble__item__t : preamble -> Pulse_Syntax_Base.st_term) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; t; c; uvs;_} -> t
let (__proj__Mkpreamble__item__c : preamble -> Pulse_Syntax_Base.comp_st) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; t; c; uvs;_} -> c
let (__proj__Mkpreamble__item__uvs : preamble -> Pulse_Typing_Env.env) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; t; c; uvs;_} -> uvs
let (pst_env :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      unit Pulse_Prover_Substs.t -> Pulse_Typing_Env.env)
  =
  fun g0 ->
    fun uvs ->
      fun ss ->
        Pulse_Typing_Env.push_env g0
          (Pulse_Prover_Util.psubst_env g0
             (Pulse_Prover_Util.filter_ss g0 uvs ss) ss)
type 'preamble1 prover_state =
  {
  ss: unit Pulse_Prover_Substs.t ;
  solved_goals: Pulse_Syntax_Base.term ;
  unsolved_goals: Pulse_Syntax_Base.term Prims.list ;
  remaining_ctxt: Pulse_Syntax_Base.term Prims.list ;
  steps: Pulse_Syntax_Base.st_term ;
  t_typing: (unit, unit, unit) Pulse_Typing.st_typing ;
  unsolved_goals_typing: unit ;
  remaining_ctxt_typing: unit ;
  steps_typing: (unit, unit, unit) Pulse_Typing.st_typing ;
  c_pre_inv: unit ;
  solved_goals_closed: unit }
let (__proj__Mkprover_state__item__ss :
  preamble -> unit prover_state -> unit Pulse_Prover_Substs.t) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { ss; solved_goals; unsolved_goals; remaining_ctxt; steps; t_typing;
          unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
          c_pre_inv; solved_goals_closed;_} -> ss
let (__proj__Mkprover_state__item__solved_goals :
  preamble -> unit prover_state -> Pulse_Syntax_Base.term) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { ss; solved_goals; unsolved_goals; remaining_ctxt; steps; t_typing;
          unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
          c_pre_inv; solved_goals_closed;_} -> solved_goals
let (__proj__Mkprover_state__item__unsolved_goals :
  preamble -> unit prover_state -> Pulse_Syntax_Base.term Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { ss; solved_goals; unsolved_goals; remaining_ctxt; steps; t_typing;
          unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
          c_pre_inv; solved_goals_closed;_} -> unsolved_goals
let (__proj__Mkprover_state__item__remaining_ctxt :
  preamble -> unit prover_state -> Pulse_Syntax_Base.term Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { ss; solved_goals; unsolved_goals; remaining_ctxt; steps; t_typing;
          unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
          c_pre_inv; solved_goals_closed;_} -> remaining_ctxt
let (__proj__Mkprover_state__item__steps :
  preamble -> unit prover_state -> Pulse_Syntax_Base.st_term) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { ss; solved_goals; unsolved_goals; remaining_ctxt; steps; t_typing;
          unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
          c_pre_inv; solved_goals_closed;_} -> steps
let (__proj__Mkprover_state__item__t_typing :
  preamble -> unit prover_state -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { ss; solved_goals; unsolved_goals; remaining_ctxt; steps; t_typing;
          unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
          c_pre_inv; solved_goals_closed;_} -> t_typing


let (__proj__Mkprover_state__item__steps_typing :
  preamble -> unit prover_state -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { ss; solved_goals; unsolved_goals; remaining_ctxt; steps; t_typing;
          unsolved_goals_typing; remaining_ctxt_typing; steps_typing;
          c_pre_inv; solved_goals_closed;_} -> steps_typing
type ('preamble1, 'p1, 'p2) pst_extends = unit
type prover_t =
  preamble ->
    unit prover_state ->
      (unit prover_state FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr
type prover_step_t =
  preamble ->
    unit prover_state ->
      prover_t ->
        (unit prover_state FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr