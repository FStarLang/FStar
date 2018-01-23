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
      let uu___50_67 = goal in
      let uu____68 = FStar_TypeChecker_Env.rename_env subst1 goal.context in
      let uu____69 = FStar_Syntax_Subst.subst subst1 goal.witness in
      let uu____70 = FStar_Syntax_Subst.subst subst1 goal.goal_ty in
      {
        context = uu____68;
        witness = uu____69;
        goal_ty = uu____70;
        opts = (uu___50_67.opts);
        is_guard = (uu___50_67.is_guard)
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
  psc: FStar_TypeChecker_Normalize.psc;
  entry_range: FStar_Range.range;}[@@deriving show]
let __proj__Mkproofstate__item__main_context:
  proofstate -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;_} -> __fname__main_context
let __proj__Mkproofstate__item__main_goal: proofstate -> goal =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;_} -> __fname__main_goal
let __proj__Mkproofstate__item__all_implicits:
  proofstate -> FStar_TypeChecker_Env.implicits =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;_} -> __fname__all_implicits
let __proj__Mkproofstate__item__goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;_} -> __fname__goals
let __proj__Mkproofstate__item__smt_goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;_} -> __fname__smt_goals
let __proj__Mkproofstate__item__depth: proofstate -> Prims.int =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;_} -> __fname__depth
let __proj__Mkproofstate__item____dump:
  proofstate -> proofstate -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;_} -> __fname____dump
let __proj__Mkproofstate__item__psc:
  proofstate -> FStar_TypeChecker_Normalize.psc =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;_} -> __fname__psc
let __proj__Mkproofstate__item__entry_range: proofstate -> FStar_Range.range
  =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;_} -> __fname__entry_range
let subst_proof_state:
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate =
  fun subst1  ->
    fun ps  ->
      let uu____321 = FStar_Options.tactic_raw_binders () in
      if uu____321
      then ps
      else
        (let uu___51_323 = ps in
         let uu____324 = subst_goal subst1 ps.main_goal in
         let uu____325 = FStar_List.map (subst_goal subst1) ps.goals in
         {
           main_context = (uu___51_323.main_context);
           main_goal = uu____324;
           all_implicits = (uu___51_323.all_implicits);
           goals = uu____325;
           smt_goals = (uu___51_323.smt_goals);
           depth = (uu___51_323.depth);
           __dump = (uu___51_323.__dump);
           psc = (uu___51_323.psc);
           entry_range = (uu___51_323.entry_range)
         })
let decr_depth: proofstate -> proofstate =
  fun ps  ->
    let uu___52_331 = ps in
    {
      main_context = (uu___52_331.main_context);
      main_goal = (uu___52_331.main_goal);
      all_implicits = (uu___52_331.all_implicits);
      goals = (uu___52_331.goals);
      smt_goals = (uu___52_331.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___52_331.__dump);
      psc = (uu___52_331.psc);
      entry_range = (uu___52_331.entry_range)
    }
let incr_depth: proofstate -> proofstate =
  fun ps  ->
    let uu___53_335 = ps in
    {
      main_context = (uu___53_335.main_context);
      main_goal = (uu___53_335.main_goal);
      all_implicits = (uu___53_335.all_implicits);
      goals = (uu___53_335.goals);
      smt_goals = (uu___53_335.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___53_335.__dump);
      psc = (uu___53_335.psc);
      entry_range = (uu___53_335.entry_range)
    }
let tracepoint: proofstate -> Prims.unit =
  fun ps  ->
    let uu____339 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____341 = FStar_Options.tactic_trace_d () in
         ps.depth <= uu____341) in
    if uu____339
    then
      let uu____342 =
        let uu____343 = FStar_TypeChecker_Normalize.psc_subst ps.psc in
        subst_proof_state uu____343 ps in
      ps.__dump uu____342 "TRACE"
    else ()
let set_ps_psc: FStar_TypeChecker_Normalize.psc -> proofstate -> proofstate =
  fun psc  ->
    fun ps  ->
      let uu___54_351 = ps in
      {
        main_context = (uu___54_351.main_context);
        main_goal = (uu___54_351.main_goal);
        all_implicits = (uu___54_351.all_implicits);
        goals = (uu___54_351.goals);
        smt_goals = (uu___54_351.smt_goals);
        depth = (uu___54_351.depth);
        __dump = (uu___54_351.__dump);
        psc;
        entry_range = (uu___54_351.entry_range)
      }
let set_proofstate_range: proofstate -> FStar_Range.range -> proofstate =
  fun ps  ->
    fun r  ->
      let uu___55_358 = ps in
      {
        main_context = (uu___55_358.main_context);
        main_goal = (uu___55_358.main_goal);
        all_implicits = (uu___55_358.all_implicits);
        goals = (uu___55_358.goals);
        smt_goals = (uu___55_358.smt_goals);
        depth = (uu___55_358.depth);
        __dump = (uu___55_358.__dump);
        psc = (uu___55_358.psc);
        entry_range = r
      }
type direction =
  | TopDown
  | BottomUp[@@deriving show]
let uu___is_TopDown: direction -> Prims.bool =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____362 -> false
let uu___is_BottomUp: direction -> Prims.bool =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____366 -> false