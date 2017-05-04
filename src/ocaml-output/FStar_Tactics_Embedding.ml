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
let embed_goal: FStar_Tactics_Basic.goal -> FStar_Syntax_Syntax.term =
  fun g  ->
    FStar_Reflection_Basic.embed_pair
      ((g.FStar_Tactics_Basic.context), (g.FStar_Tactics_Basic.goal_ty))
      FStar_Reflection_Basic.embed_env FStar_Reflection_Data.fstar_refl_env
      FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term
let unembed_goal:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal
  =
  fun env  ->
    fun t  ->
      let uu____29 =
        FStar_Reflection_Basic.unembed_pair t
          (FStar_Reflection_Basic.unembed_env env)
          FStar_Reflection_Basic.unembed_term in
      match uu____29 with
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
      let uu____91 =
        let uu____92 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____93 =
          let uu____94 = FStar_Syntax_Syntax.iarg t_a in
          let uu____95 =
            let uu____97 =
              let uu____98 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____98 in
            let uu____99 =
              let uu____101 =
                let uu____102 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____102 in
              [uu____101] in
            uu____97 :: uu____99 in
          uu____94 :: uu____95 in
        FStar_Syntax_Syntax.mk_Tm_app uu____92 uu____93 in
      uu____91 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps) ->
      let uu____111 =
        let uu____112 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____113 =
          let uu____114 = FStar_Syntax_Syntax.iarg t_a in
          let uu____115 =
            let uu____117 =
              let uu____118 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____118 in
            let uu____119 =
              let uu____121 =
                let uu____122 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____122 in
              [uu____121] in
            uu____117 :: uu____119 in
          uu____114 :: uu____115 in
        FStar_Syntax_Syntax.mk_Tm_app uu____112 uu____113 in
      uu____111 None FStar_Range.dummyRange
let unembed_result env res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____158 = FStar_Syntax_Util.head_and_args res1 in
  match uu____158 with
  | (hd1,args) ->
      let uu____190 =
        let uu____198 =
          let uu____199 = FStar_Syntax_Util.un_uinst hd1 in
          uu____199.FStar_Syntax_Syntax.n in
        (uu____198, args) in
      (match uu____190 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____216)::(embedded_state,uu____218)::[]) when
           let uu____252 = fstar_tactics_lid "Success" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____252 ->
           let uu____253 =
             let uu____256 = unembed_a a in
             let uu____257 = unembed_state env embedded_state in
             (uu____256, uu____257) in
           FStar_Util.Inl uu____253
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____265)::(embedded_state,uu____267)::[])
           when
           let uu____301 = fstar_tactics_lid "Failed" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____301 ->
           let uu____302 =
             let uu____305 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____306 = unembed_state env embedded_state in
             (uu____305, uu____306) in
           FStar_Util.Inr uu____302
       | uu____311 ->
           let uu____319 =
             let uu____320 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____320 in
           failwith uu____319)