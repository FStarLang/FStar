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
let t_bool:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = FStar_TypeChecker_Common.t_bool
let t_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = FStar_TypeChecker_Common.t_string
let fstar_tac_prefix_typ:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  let uu____26 =
    let uu____27 =
      let uu____28 = lid_as_tm FStar_Syntax_Const.list_lid in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____28 [FStar_Syntax_Syntax.U_zero] in
    let uu____29 =
      let uu____30 = FStar_Syntax_Syntax.as_arg t_string in [uu____30] in
    FStar_Syntax_Syntax.mk_Tm_app uu____27 uu____29 in
  uu____26 None FStar_Range.dummyRange
let fstar_tac_nselt_typ:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  let uu____37 =
    let uu____38 =
      let uu____39 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____39
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____40 =
      let uu____41 = FStar_Syntax_Syntax.as_arg fstar_tac_prefix_typ in
      let uu____42 =
        let uu____44 = FStar_Syntax_Syntax.as_arg t_bool in [uu____44] in
      uu____41 :: uu____42 in
    FStar_Syntax_Syntax.mk_Tm_app uu____38 uu____40 in
  uu____37 None FStar_Range.dummyRange
let fstar_tac_ns_typ:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  let uu____51 =
    let uu____52 =
      let uu____53 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____53
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____54 =
      let uu____55 = FStar_Syntax_Syntax.as_arg fstar_tac_nselt_typ in
      let uu____56 =
        let uu____58 = FStar_Syntax_Syntax.as_arg t_bool in [uu____58] in
      uu____55 :: uu____56 in
    FStar_Syntax_Syntax.mk_Tm_app uu____52 uu____54 in
  uu____51 None FStar_Range.dummyRange
let embed_proof_namespace:
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Env.proof_namespace -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun ns  ->
      let embed_prefix prf =
        FStar_Reflection_Basic.embed_list FStar_Reflection_Basic.embed_string
          t_string prf in
      let embed_elt e =
        FStar_Reflection_Basic.embed_pair embed_prefix fstar_tac_prefix_typ
          FStar_Reflection_Basic.embed_bool t_bool e in
      let uu____86 = FStar_List.hd ns in
      FStar_Reflection_Basic.embed_list embed_elt fstar_tac_nselt_typ
        uu____86
let unembed_proof_namespace:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term ->
      (Prims.string Prims.list* Prims.bool) Prims.list Prims.list
  =
  fun ps  ->
    fun t  ->
      let orig_ns =
        FStar_TypeChecker_Env.get_proof_ns
          ps.FStar_Tactics_Basic.main_context in
      let hd1 =
        FStar_Reflection_Basic.unembed_list
          (FStar_Reflection_Basic.unembed_pair
             (FStar_Reflection_Basic.unembed_list
                FStar_Reflection_Basic.unembed_string)
             FStar_Reflection_Basic.unembed_bool) t in
      hd1 :: orig_ns
let embed_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun ps  ->
    fun env  ->
      let uu____120 =
        let uu____121 =
          let uu____125 = FStar_TypeChecker_Env.all_binders env in
          let uu____126 = FStar_TypeChecker_Env.get_proof_ns env in
          (uu____125, uu____126) in
        FStar_Reflection_Basic.embed_pair
          (FStar_Reflection_Basic.embed_list
             FStar_Reflection_Basic.embed_binder
             FStar_Reflection_Data.fstar_refl_binder)
          FStar_Reflection_Data.fstar_refl_binders (embed_proof_namespace ps)
          fstar_tac_ns_typ uu____121 in
      FStar_Reflection_Basic.protect_embedded_term
        FStar_Reflection_Data.fstar_refl_env uu____120
let unembed_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun ps  ->
    fun protected_embedded_env  ->
      let embedded_env =
        FStar_Reflection_Basic.un_protect_embedded_term
          protected_embedded_env in
      let uu____135 =
        FStar_Reflection_Basic.unembed_pair
          (FStar_Reflection_Basic.unembed_list
             FStar_Reflection_Basic.unembed_binder)
          (unembed_proof_namespace ps) embedded_env in
      match uu____135 with
      | (binders,ns) ->
          let env = ps.FStar_Tactics_Basic.main_context in
          let env1 = FStar_TypeChecker_Env.set_proof_ns ns env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun b  ->
                   let uu____153 =
                     FStar_TypeChecker_Env.try_lookup_bv env2 (Prims.fst b) in
                   match uu____153 with
                   | None  -> FStar_TypeChecker_Env.push_binders env2 [b]
                   | uu____163 -> env2) env1 binders in
          env2
let embed_goal:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Basic.goal -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun g  ->
      FStar_Reflection_Basic.embed_pair (embed_env ps)
        FStar_Reflection_Data.fstar_refl_env
        FStar_Reflection_Basic.embed_term
        FStar_Reflection_Data.fstar_refl_term
        ((g.FStar_Tactics_Basic.context), (g.FStar_Tactics_Basic.goal_ty))
let unembed_goal:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal
  =
  fun ps  ->
    fun t  ->
      let uu____179 =
        FStar_Reflection_Basic.unembed_pair (unembed_env ps)
          FStar_Reflection_Basic.unembed_term t in
      match uu____179 with
      | (env,goal_ty) ->
          {
            FStar_Tactics_Basic.context = env;
            FStar_Tactics_Basic.witness = None;
            FStar_Tactics_Basic.goal_ty = goal_ty
          }
let embed_goals:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Basic.goal Prims.list -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun l  ->
      FStar_Reflection_Basic.embed_list (embed_goal ps) fstar_tactics_goal l
let unembed_goals:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal Prims.list
  =
  fun ps  ->
    fun egs  -> FStar_Reflection_Basic.unembed_list (unembed_goal ps) egs
type state =
  (FStar_Tactics_Basic.goal Prims.list* FStar_Tactics_Basic.goal Prims.list)
let embed_state:
  FStar_Tactics_Basic.proofstate -> state -> FStar_Syntax_Syntax.term =
  fun ps  ->
    fun s  ->
      FStar_Reflection_Basic.embed_pair (embed_goals ps) fstar_tactics_goals
        (embed_goals ps) fstar_tactics_goals s
let unembed_state:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term ->
      (FStar_Tactics_Basic.goal Prims.list* FStar_Tactics_Basic.goal
        Prims.list)
  =
  fun ps  ->
    fun s  ->
      let s1 = FStar_Syntax_Util.unascribe s in
      FStar_Reflection_Basic.unembed_pair (unembed_goals ps)
        (unembed_goals ps) s1
let embed_result ps res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps1) ->
      let uu____252 =
        let uu____253 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____254 =
          let uu____255 = FStar_Syntax_Syntax.iarg t_a in
          let uu____256 =
            let uu____258 =
              let uu____259 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____259 in
            let uu____260 =
              let uu____262 =
                let uu____263 =
                  embed_state ps1
                    ((ps1.FStar_Tactics_Basic.goals),
                      (ps1.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____263 in
              [uu____262] in
            uu____258 :: uu____260 in
          uu____255 :: uu____256 in
        FStar_Syntax_Syntax.mk_Tm_app uu____253 uu____254 in
      uu____252 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____272 =
        let uu____273 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____274 =
          let uu____275 = FStar_Syntax_Syntax.iarg t_a in
          let uu____276 =
            let uu____278 =
              let uu____279 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____279 in
            let uu____280 =
              let uu____282 =
                let uu____283 =
                  embed_state ps1
                    ((ps1.FStar_Tactics_Basic.goals),
                      (ps1.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____283 in
              [uu____282] in
            uu____278 :: uu____280 in
          uu____275 :: uu____276 in
        FStar_Syntax_Syntax.mk_Tm_app uu____273 uu____274 in
      uu____272 None FStar_Range.dummyRange
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____319 = FStar_Syntax_Util.head_and_args res1 in
  match uu____319 with
  | (hd1,args) ->
      let uu____351 =
        let uu____359 =
          let uu____360 = FStar_Syntax_Util.un_uinst hd1 in
          uu____360.FStar_Syntax_Syntax.n in
        (uu____359, args) in
      (match uu____351 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____377)::(embedded_state,uu____379)::[]) when
           let uu____413 = fstar_tactics_lid "Success" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____413 ->
           let uu____414 =
             let uu____417 = unembed_a a in
             let uu____418 = unembed_state ps embedded_state in
             (uu____417, uu____418) in
           FStar_Util.Inl uu____414
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____426)::(embedded_state,uu____428)::[])
           when
           let uu____462 = fstar_tactics_lid "Failed" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____462 ->
           let uu____463 =
             let uu____466 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____467 = unembed_state ps embedded_state in
             (uu____466, uu____467) in
           FStar_Util.Inr uu____463
       | uu____472 ->
           let uu____480 =
             let uu____481 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____481 in
           failwith uu____480)