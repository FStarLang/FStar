open Prims
type goal =
  {
  context: FStar_TypeChecker_Env.env;
  witness: FStar_Syntax_Syntax.term;
  goal_ty: FStar_Syntax_Syntax.typ;
  opts: FStar_Options.optionstate;
  is_guard: Prims.bool;}[@@deriving show]
let __proj__Mkgoal__item__context: goal -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__context
let __proj__Mkgoal__item__witness: goal -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__witness
let __proj__Mkgoal__item__goal_ty: goal -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__goal_ty
let __proj__Mkgoal__item__opts: goal -> FStar_Options.optionstate =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__opts
let __proj__Mkgoal__item__is_guard: goal -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__is_guard
let subst_goal: FStar_Syntax_Syntax.subst_t -> goal -> goal =
  fun subst1  ->
    fun goal  ->
      let uu___128_74 = goal in
      let uu____75 = FStar_TypeChecker_Env.rename_env subst1 goal.context in
      let uu____76 = FStar_Syntax_Subst.subst subst1 goal.witness in
      let uu____77 = FStar_Syntax_Subst.subst subst1 goal.goal_ty in
      {
        context = uu____75;
        witness = uu____76;
        goal_ty = uu____77;
        opts = (uu___128_74.opts);
        is_guard = (uu___128_74.is_guard)
      }
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env;
  main_goal: goal;
  all_implicits: FStar_TypeChecker_Env.implicits;
  goals: goal Prims.list;
  smt_goals: goal Prims.list;
  depth: Prims.int;
  __dump: proofstate -> Prims.string -> Prims.unit;
  psc: FStar_TypeChecker_Normalize.psc;}[@@deriving show]
let __proj__Mkproofstate__item__main_context:
  proofstate -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;_} ->
        __fname__main_context
let __proj__Mkproofstate__item__main_goal: proofstate -> goal =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;_} -> __fname__main_goal
let __proj__Mkproofstate__item__all_implicits:
  proofstate -> FStar_TypeChecker_Env.implicits =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;_} ->
        __fname__all_implicits
let __proj__Mkproofstate__item__goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;_} -> __fname__goals
let __proj__Mkproofstate__item__smt_goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;_} -> __fname__smt_goals
let __proj__Mkproofstate__item__depth: proofstate -> Prims.int =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;_} -> __fname__depth
let __proj__Mkproofstate__item____dump:
  proofstate -> proofstate -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;_} -> __fname____dump
let __proj__Mkproofstate__item__psc:
  proofstate -> FStar_TypeChecker_Normalize.psc =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;_} -> __fname__psc
let subst_proof_state:
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate =
  fun subst1  ->
    fun ps  ->
      let uu___129_308 = ps in
      let uu____309 = subst_goal subst1 ps.main_goal in
      let uu____310 = FStar_List.map (subst_goal subst1) ps.goals in
      {
        main_context = (uu___129_308.main_context);
        main_goal = uu____309;
        all_implicits = (uu___129_308.all_implicits);
        goals = uu____310;
        smt_goals = (uu___129_308.smt_goals);
        depth = (uu___129_308.depth);
        __dump = (uu___129_308.__dump);
        psc = (uu___129_308.psc)
      }
let decr_depth: proofstate -> proofstate =
  fun ps  ->
    let uu___130_317 = ps in
    {
      main_context = (uu___130_317.main_context);
      main_goal = (uu___130_317.main_goal);
      all_implicits = (uu___130_317.all_implicits);
      goals = (uu___130_317.goals);
      smt_goals = (uu___130_317.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___130_317.__dump);
      psc = (uu___130_317.psc)
    }
let incr_depth: proofstate -> proofstate =
  fun ps  ->
    let uu___131_322 = ps in
    {
      main_context = (uu___131_322.main_context);
      main_goal = (uu___131_322.main_goal);
      all_implicits = (uu___131_322.all_implicits);
      goals = (uu___131_322.goals);
      smt_goals = (uu___131_322.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___131_322.__dump);
      psc = (uu___131_322.psc)
    }
let tracepoint: proofstate -> Prims.unit =
  fun ps  ->
    let uu____327 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____329 = FStar_Options.tactic_trace_d () in
         ps.depth <= uu____329) in
    if uu____327 then ps.__dump ps "TRACE" else ()
let set_ps_psc: FStar_TypeChecker_Normalize.psc -> proofstate -> proofstate =
  fun psc  ->
    fun ps  ->
      let uu___132_339 = ps in
      {
        main_context = (uu___132_339.main_context);
        main_goal = (uu___132_339.main_goal);
        all_implicits = (uu___132_339.all_implicits);
        goals = (uu___132_339.goals);
        smt_goals = (uu___132_339.smt_goals);
        depth = (uu___132_339.depth);
        __dump = (uu___132_339.__dump);
        psc
      }
type direction =
  | TopDown
  | BottomUp[@@deriving show]
let uu___is_TopDown: direction -> Prims.bool =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____344 -> false
let uu___is_BottomUp: direction -> Prims.bool =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____349 -> false