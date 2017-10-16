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
      let uu___113_74 = goal in
      let uu____75 = FStar_TypeChecker_Env.rename_env subst1 goal.context in
      let uu____76 = FStar_Syntax_Subst.subst subst1 goal.witness in
      let uu____77 = FStar_Syntax_Subst.subst subst1 goal.goal_ty in
      {
        context = uu____75;
        witness = uu____76;
        goal_ty = uu____77;
        opts = (uu___113_74.opts);
        is_guard = (uu___113_74.is_guard)
      }
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env;
  main_goal: goal;
  all_implicits: FStar_TypeChecker_Env.implicits;
  goals: goal Prims.list;
  smt_goals: goal Prims.list;
  depth: Prims.int;
  __dump: proofstate -> Prims.string -> Prims.unit;}[@@deriving show]
let __proj__Mkproofstate__item__main_context:
  proofstate -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump;_} -> __fname__main_context
let __proj__Mkproofstate__item__main_goal: proofstate -> goal =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump;_} -> __fname__main_goal
let __proj__Mkproofstate__item__all_implicits:
  proofstate -> FStar_TypeChecker_Env.implicits =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump;_} -> __fname__all_implicits
let __proj__Mkproofstate__item__goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump;_} -> __fname__goals
let __proj__Mkproofstate__item__smt_goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump;_} -> __fname__smt_goals
let __proj__Mkproofstate__item__depth: proofstate -> Prims.int =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump;_} -> __fname__depth
let __proj__Mkproofstate__item____dump:
  proofstate -> proofstate -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump;_} -> __fname____dump
let subst_proof_state:
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate =
  fun subst1  ->
    fun ps  ->
      let uu___114_277 = ps in
      let uu____278 = subst_goal subst1 ps.main_goal in
      let uu____279 = FStar_List.map (subst_goal subst1) ps.goals in
      {
        main_context = (uu___114_277.main_context);
        main_goal = uu____278;
        all_implicits = (uu___114_277.all_implicits);
        goals = uu____279;
        smt_goals = (uu___114_277.smt_goals);
        depth = (uu___114_277.depth);
        __dump = (uu___114_277.__dump)
      }
let decr_depth: proofstate -> proofstate =
  fun ps  ->
    let uu___115_286 = ps in
    {
      main_context = (uu___115_286.main_context);
      main_goal = (uu___115_286.main_goal);
      all_implicits = (uu___115_286.all_implicits);
      goals = (uu___115_286.goals);
      smt_goals = (uu___115_286.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___115_286.__dump)
    }
let incr_depth: proofstate -> proofstate =
  fun ps  ->
    let uu___116_291 = ps in
    {
      main_context = (uu___116_291.main_context);
      main_goal = (uu___116_291.main_goal);
      all_implicits = (uu___116_291.all_implicits);
      goals = (uu___116_291.goals);
      smt_goals = (uu___116_291.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___116_291.__dump)
    }
let tracepoint: proofstate -> Prims.unit =
  fun ps  ->
    let uu____296 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____298 = FStar_Options.tactic_trace_d () in
         ps.depth <= uu____298) in
    if uu____296 then ps.__dump ps "TRACE" else ()
type direction =
  | TopDown
  | BottomUp[@@deriving show]
let uu___is_TopDown: direction -> Prims.bool =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____304 -> false
let uu___is_BottomUp: direction -> Prims.bool =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____309 -> false