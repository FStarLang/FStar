open Prims
type goal =
  {
  context: FStar_TypeChecker_Env.env ;
  witness: FStar_Syntax_Syntax.term ;
  goal_ty: FStar_Syntax_Syntax.typ ;
  opts: FStar_Options.optionstate ;
  is_guard: Prims.bool }[@@deriving show]
let (__proj__Mkgoal__item__context : goal -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__context
  
let (__proj__Mkgoal__item__witness : goal -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__witness
  
let (__proj__Mkgoal__item__goal_ty : goal -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__goal_ty
  
let (__proj__Mkgoal__item__opts : goal -> FStar_Options.optionstate) =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__opts
  
let (__proj__Mkgoal__item__is_guard : goal -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__is_guard
  
let (subst_goal : FStar_Syntax_Syntax.subst_t -> goal -> goal) =
  fun subst1  ->
    fun goal  ->
      let uu___53_81 = goal  in
      let uu____82 = FStar_TypeChecker_Env.rename_env subst1 goal.context  in
      let uu____83 = FStar_Syntax_Subst.subst subst1 goal.witness  in
      let uu____84 = FStar_Syntax_Subst.subst subst1 goal.goal_ty  in
      {
        context = uu____82;
        witness = uu____83;
        goal_ty = uu____84;
        opts = (uu___53_81.opts);
        is_guard = (uu___53_81.is_guard)
      }
  
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop [@@deriving show]
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Goal  -> true | uu____90 -> false 
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | SMT  -> true | uu____96 -> false 
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Force  -> true | uu____102 -> false
  
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Drop  -> true | uu____108 -> false 
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env ;
  main_goal: goal ;
  all_implicits: FStar_TypeChecker_Env.implicits ;
  goals: goal Prims.list ;
  smt_goals: goal Prims.list ;
  depth: Prims.int ;
  __dump: proofstate -> Prims.string -> unit ;
  psc: FStar_TypeChecker_Normalize.psc ;
  entry_range: FStar_Range.range ;
  guard_policy: guard_policy ;
  freshness: Prims.int }[@@deriving show]
let (__proj__Mkproofstate__item__main_context :
  proofstate -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__main_context
  
let (__proj__Mkproofstate__item__main_goal : proofstate -> goal) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__main_goal
  
let (__proj__Mkproofstate__item__all_implicits :
  proofstate -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__all_implicits
  
let (__proj__Mkproofstate__item__goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__goals
  
let (__proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__smt_goals
  
let (__proj__Mkproofstate__item__depth : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__depth
  
let (__proj__Mkproofstate__item____dump :
  proofstate -> proofstate -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname____dump
  
let (__proj__Mkproofstate__item__psc :
  proofstate -> FStar_TypeChecker_Normalize.psc) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__psc
  
let (__proj__Mkproofstate__item__entry_range :
  proofstate -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__entry_range
  
let (__proj__Mkproofstate__item__guard_policy : proofstate -> guard_policy) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__guard_policy
  
let (__proj__Mkproofstate__item__freshness : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy;
        freshness = __fname__freshness;_} -> __fname__freshness
  
let (subst_proof_state :
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate) =
  fun subst1  ->
    fun ps  ->
      let uu____483 = FStar_Options.tactic_raw_binders ()  in
      if uu____483
      then ps
      else
        (let uu___54_485 = ps  in
         let uu____486 = subst_goal subst1 ps.main_goal  in
         let uu____487 = FStar_List.map (subst_goal subst1) ps.goals  in
         {
           main_context = (uu___54_485.main_context);
           main_goal = uu____486;
           all_implicits = (uu___54_485.all_implicits);
           goals = uu____487;
           smt_goals = (uu___54_485.smt_goals);
           depth = (uu___54_485.depth);
           __dump = (uu___54_485.__dump);
           psc = (uu___54_485.psc);
           entry_range = (uu___54_485.entry_range);
           guard_policy = (uu___54_485.guard_policy);
           freshness = (uu___54_485.freshness)
         })
  
let (decr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___55_495 = ps  in
    {
      main_context = (uu___55_495.main_context);
      main_goal = (uu___55_495.main_goal);
      all_implicits = (uu___55_495.all_implicits);
      goals = (uu___55_495.goals);
      smt_goals = (uu___55_495.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___55_495.__dump);
      psc = (uu___55_495.psc);
      entry_range = (uu___55_495.entry_range);
      guard_policy = (uu___55_495.guard_policy);
      freshness = (uu___55_495.freshness)
    }
  
let (incr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___56_501 = ps  in
    {
      main_context = (uu___56_501.main_context);
      main_goal = (uu___56_501.main_goal);
      all_implicits = (uu___56_501.all_implicits);
      goals = (uu___56_501.goals);
      smt_goals = (uu___56_501.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___56_501.__dump);
      psc = (uu___56_501.psc);
      entry_range = (uu___56_501.entry_range);
      guard_policy = (uu___56_501.guard_policy);
      freshness = (uu___56_501.freshness)
    }
  
let (tracepoint : proofstate -> unit) =
  fun ps  ->
    let uu____507 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____509 = FStar_Options.tactic_trace_d ()  in
         ps.depth <= uu____509)
       in
    if uu____507
    then
      let uu____510 =
        let uu____511 = FStar_TypeChecker_Normalize.psc_subst ps.psc  in
        subst_proof_state uu____511 ps  in
      ps.__dump uu____510 "TRACE"
    else ()
  
let (set_ps_psc :
  FStar_TypeChecker_Normalize.psc -> proofstate -> proofstate) =
  fun psc  ->
    fun ps  ->
      let uu___57_523 = ps  in
      {
        main_context = (uu___57_523.main_context);
        main_goal = (uu___57_523.main_goal);
        all_implicits = (uu___57_523.all_implicits);
        goals = (uu___57_523.goals);
        smt_goals = (uu___57_523.smt_goals);
        depth = (uu___57_523.depth);
        __dump = (uu___57_523.__dump);
        psc;
        entry_range = (uu___57_523.entry_range);
        guard_policy = (uu___57_523.guard_policy);
        freshness = (uu___57_523.freshness)
      }
  
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps  ->
    fun r  ->
      let uu___58_534 = ps  in
      {
        main_context = (uu___58_534.main_context);
        main_goal = (uu___58_534.main_goal);
        all_implicits = (uu___58_534.all_implicits);
        goals = (uu___58_534.goals);
        smt_goals = (uu___58_534.smt_goals);
        depth = (uu___58_534.depth);
        __dump = (uu___58_534.__dump);
        psc = (uu___58_534.psc);
        entry_range = r;
        guard_policy = (uu___58_534.guard_policy);
        freshness = (uu___58_534.freshness)
      }
  
type direction =
  | TopDown 
  | BottomUp [@@deriving show]
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____540 -> false
  
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____546 -> false
  