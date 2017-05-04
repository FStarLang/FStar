open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid: Prims.string -> FStar_Ident.lident =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Tactics"] [s])
      FStar_Range.dummyRange
let by_tactic_lid: FStar_Ident.lident = fstar_tactics_lid "by_tactic"
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____7 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None in
    FStar_All.pipe_right uu____7 FStar_Syntax_Syntax.fv_to_tm
let mk_tactic_lid_as_term: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  -> let uu____11 = fstar_tactics_lid s in lid_as_tm uu____11
let fstar_tactics_goal: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goal"
let fstar_tactics_goals: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goals"
let fstar_tactics_term_view: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "term_view"
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____15 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____15
let fstar_tactics_lid_as_data_tm: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  -> let uu____19 = fstar_tactics_lid s in lid_as_data_tm uu____19
let fstar_tactics_Failed: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Failed"
let fstar_tactics_Success: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Success"
let embed_env:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    let uu____23 =
      let uu____24 = FStar_TypeChecker_Env.all_binders env in
      FStar_Reflection_Basic.embed_list FStar_Reflection_Basic.embed_binder
        FStar_Reflection_Data.fstar_refl_binder uu____24 in
    FStar_Reflection_Basic.protect_embedded_term
      FStar_Reflection_Data.fstar_refl_env uu____23
let unembed_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun protected_embedded_env  ->
      let embedded_env =
        FStar_Reflection_Basic.un_protect_embedded_term
          protected_embedded_env in
      let binders =
        FStar_Reflection_Basic.unembed_list
          FStar_Reflection_Basic.unembed_binder embedded_env in
      FStar_List.fold_left
        (fun env1  ->
           fun b  ->
             let uu____41 =
               FStar_TypeChecker_Env.try_lookup_bv env1 (Prims.fst b) in
             match uu____41 with
             | None  -> FStar_TypeChecker_Env.push_binders env1 [b]
             | uu____51 -> env1) env binders
let embed_goal: FStar_Tactics_Basic.goal -> FStar_Syntax_Syntax.term =
  fun g  ->
    FStar_Reflection_Basic.embed_pair
      ((g.FStar_Tactics_Basic.context), (g.FStar_Tactics_Basic.goal_ty))
      embed_env FStar_Reflection_Data.fstar_refl_env
      FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term
let unembed_goal:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal
  =
  fun env  ->
    fun t  ->
      let uu____64 =
        FStar_Reflection_Basic.unembed_pair t (unembed_env env)
          FStar_Reflection_Basic.unembed_term in
      match uu____64 with
      | (env1,goal_ty) ->
          {
            FStar_Tactics_Basic.context = env1;
            FStar_Tactics_Basic.witness = None;
            FStar_Tactics_Basic.goal_ty = goal_ty
          }
let embed_goals:
  FStar_Tactics_Basic.goal Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> FStar_Reflection_Basic.embed_list embed_goal fstar_tactics_goal l
let unembed_goals:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal Prims.list
  =
  fun env  ->
    fun egs  -> FStar_Reflection_Basic.unembed_list (unembed_goal env) egs
type state =
  (FStar_Tactics_Basic.goal Prims.list* FStar_Tactics_Basic.goal Prims.list)
let embed_state: state -> FStar_Syntax_Syntax.term =
  fun s  ->
    FStar_Reflection_Basic.embed_pair s embed_goals fstar_tactics_goals
      embed_goals fstar_tactics_goals
let unembed_state:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Tactics_Basic.goal Prims.list* FStar_Tactics_Basic.goal
        Prims.list)
  =
  fun env  ->
    fun s  ->
      let s1 = FStar_Syntax_Util.unascribe s in
      FStar_Reflection_Basic.unembed_pair s1 (unembed_goals env)
        (unembed_goals env)
let embed_result res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps) ->
      let uu____126 =
        let uu____127 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____128 =
          let uu____129 = FStar_Syntax_Syntax.iarg t_a in
          let uu____130 =
            let uu____132 =
              let uu____133 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____133 in
            let uu____134 =
              let uu____136 =
                let uu____137 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____137 in
              [uu____136] in
            uu____132 :: uu____134 in
          uu____129 :: uu____130 in
        FStar_Syntax_Syntax.mk_Tm_app uu____127 uu____128 in
      uu____126 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps) ->
      let uu____146 =
        let uu____147 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____148 =
          let uu____149 = FStar_Syntax_Syntax.iarg t_a in
          let uu____150 =
            let uu____152 =
              let uu____153 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____153 in
            let uu____154 =
              let uu____156 =
                let uu____157 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____157 in
              [uu____156] in
            uu____152 :: uu____154 in
          uu____149 :: uu____150 in
        FStar_Syntax_Syntax.mk_Tm_app uu____147 uu____148 in
      uu____146 None FStar_Range.dummyRange
let unembed_result env res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____193 = FStar_Syntax_Util.head_and_args res1 in
  match uu____193 with
  | (hd1,args) ->
      let uu____225 =
        let uu____233 =
          let uu____234 = FStar_Syntax_Util.un_uinst hd1 in
          uu____234.FStar_Syntax_Syntax.n in
        (uu____233, args) in
      (match uu____225 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____251)::(embedded_state,uu____253)::[]) when
           let uu____287 = fstar_tactics_lid "Success" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____287 ->
           let uu____288 =
             let uu____291 = unembed_a a in
             let uu____292 = unembed_state env embedded_state in
             (uu____291, uu____292) in
           FStar_Util.Inl uu____288
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____300)::(embedded_state,uu____302)::[])
           when
           let uu____336 = fstar_tactics_lid "Failed" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____336 ->
           let uu____337 =
             let uu____340 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____341 = unembed_state env embedded_state in
             (uu____340, uu____341) in
           FStar_Util.Inr uu____337
       | uu____346 ->
           let uu____354 =
             let uu____355 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____355 in
           failwith uu____354)