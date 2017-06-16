open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid': Prims.string Prims.list -> FStar_Ident.lid =
  fun s  -> FStar_Syntax_Const.fstar_tactics_lid' s
let fstar_tactics_lid: Prims.string -> FStar_Ident.lid =
  fun s  -> FStar_Syntax_Const.fstar_tactics_lid s
let by_tactic_lid: FStar_Ident.lid = FStar_Syntax_Const.by_tactic_lid
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____12 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None in
    FStar_All.pipe_right uu____12 FStar_Syntax_Syntax.fv_to_tm
let mk_tactic_lid_as_term: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____16 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____16
let fstar_tactics_goal: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goal"
let fstar_tactics_goals: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goals"
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____20 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____20
let fstar_tactics_lid_as_data_tm: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____24 = fstar_tactics_lid' ["Effect"; s] in
    lid_as_data_tm uu____24
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
  let uu____31 =
    let uu____32 =
      let uu____33 = lid_as_tm FStar_Syntax_Const.list_lid in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____33 [FStar_Syntax_Syntax.U_zero] in
    let uu____34 =
      let uu____35 = FStar_Syntax_Syntax.as_arg t_string in [uu____35] in
    FStar_Syntax_Syntax.mk_Tm_app uu____32 uu____34 in
  uu____31 None FStar_Range.dummyRange
let pair_typ:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____48 =
        let uu____49 =
          let uu____50 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____50
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____51 =
          let uu____52 = FStar_Syntax_Syntax.as_arg t in
          let uu____53 =
            let uu____55 = FStar_Syntax_Syntax.as_arg s in [uu____55] in
          uu____52 :: uu____53 in
        FStar_Syntax_Syntax.mk_Tm_app uu____49 uu____51 in
      uu____48 None FStar_Range.dummyRange
let fstar_tac_nselt_typ:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = pair_typ fstar_tac_prefix_typ t_bool
let fstar_tac_ns_typ:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = pair_typ fstar_tac_nselt_typ t_bool
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
      let uu____87 = FStar_List.hd ns in
      FStar_Reflection_Basic.embed_list embed_elt fstar_tac_nselt_typ
        uu____87
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
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun env  -> FStar_Syntax_Util.mk_alien env "tactics_embed_env" None
let unembed_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun ps  ->
    fun t  ->
      let uu____127 = FStar_Syntax_Util.un_alien t in
      FStar_All.pipe_right uu____127 FStar_Dyn.undyn
let embed_witness:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun ps  -> fun w  -> FStar_Reflection_Basic.embed_term w
let unembed_witness:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun ps  -> fun t  -> FStar_Reflection_Basic.unembed_term t
let embed_goal:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Basic.goal -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun g  ->
      let uu____146 =
        pair_typ FStar_Reflection_Data.fstar_refl_env
          FStar_Reflection_Data.fstar_refl_term in
      FStar_Reflection_Basic.embed_pair
        (FStar_Reflection_Basic.embed_pair (embed_env ps)
           FStar_Reflection_Data.fstar_refl_env
           FStar_Reflection_Basic.embed_term
           FStar_Reflection_Data.fstar_refl_term) uu____146
        (embed_witness ps) FStar_Reflection_Data.fstar_refl_term
        (((g.FStar_Tactics_Basic.context), (g.FStar_Tactics_Basic.goal_ty)),
          (g.FStar_Tactics_Basic.witness))
let unembed_goal:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal
  =
  fun ps  ->
    fun t  ->
      let uu____157 =
        FStar_Reflection_Basic.unembed_pair
          (FStar_Reflection_Basic.unembed_pair (unembed_env ps)
             FStar_Reflection_Basic.unembed_term) (unembed_witness ps) t in
      match uu____157 with
      | ((env,goal_ty),witness) ->
          {
            FStar_Tactics_Basic.context = env;
            FStar_Tactics_Basic.witness = witness;
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
let embed_proofstate:
  FStar_Tactics_Basic.proofstate -> FStar_Syntax_Syntax.term =
  fun ps  -> FStar_Syntax_Util.mk_alien ps "tactics.embed_proofstate" None
let unembed_proofstate:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.proofstate
  =
  fun ps  ->
    fun t  ->
      let uu____194 = FStar_Syntax_Util.un_alien t in
      FStar_All.pipe_right uu____194 FStar_Dyn.undyn
let embed_result ps res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps1) ->
      let uu____226 =
        let uu____227 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____228 =
          let uu____229 = FStar_Syntax_Syntax.iarg t_a in
          let uu____230 =
            let uu____232 =
              let uu____233 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____233 in
            let uu____234 =
              let uu____236 =
                let uu____237 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____237 in
              [uu____236] in
            uu____232 :: uu____234 in
          uu____229 :: uu____230 in
        FStar_Syntax_Syntax.mk_Tm_app uu____227 uu____228 in
      uu____226 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____244 =
        let uu____245 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____246 =
          let uu____247 = FStar_Syntax_Syntax.iarg t_a in
          let uu____248 =
            let uu____250 =
              let uu____251 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____251 in
            let uu____252 =
              let uu____254 =
                let uu____255 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____255 in
              [uu____254] in
            uu____250 :: uu____252 in
          uu____247 :: uu____248 in
        FStar_Syntax_Syntax.mk_Tm_app uu____245 uu____246 in
      uu____244 None FStar_Range.dummyRange
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____289 = FStar_Syntax_Util.head_and_args res1 in
  match uu____289 with
  | (hd1,args) ->
      let uu____321 =
        let uu____329 =
          let uu____330 = FStar_Syntax_Util.un_uinst hd1 in
          uu____330.FStar_Syntax_Syntax.n in
        (uu____329, args) in
      (match uu____321 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____347)::(embedded_state,uu____349)::[]) when
           let uu____383 = fstar_tactics_lid' ["Effect"; "Success"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____383 ->
           let uu____384 =
             let uu____387 = unembed_a a in
             let uu____388 = unembed_proofstate ps embedded_state in
             (uu____387, uu____388) in
           FStar_Util.Inl uu____384
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____396)::(embedded_state,uu____398)::[])
           when
           let uu____432 = fstar_tactics_lid' ["Effect"; "Failed"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____432 ->
           let uu____433 =
             let uu____436 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____437 = unembed_proofstate ps embedded_state in
             (uu____436, uu____437) in
           FStar_Util.Inr uu____433
       | uu____442 ->
           let uu____450 =
             let uu____451 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____451 in
           failwith uu____450)