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
let pair_typ:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____43 =
        let uu____44 =
          let uu____45 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____45
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____46 =
          let uu____47 = FStar_Syntax_Syntax.as_arg t in
          let uu____48 =
            let uu____50 = FStar_Syntax_Syntax.as_arg s in [uu____50] in
          uu____47 :: uu____48 in
        FStar_Syntax_Syntax.mk_Tm_app uu____44 uu____46 in
      uu____43 None FStar_Range.dummyRange
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
      let uu____82 = FStar_List.hd ns in
      FStar_Reflection_Basic.embed_list embed_elt fstar_tac_nselt_typ
        uu____82
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
      let uu____116 =
        let uu____117 =
          let uu____121 = FStar_TypeChecker_Env.all_binders env in
          let uu____122 = FStar_TypeChecker_Env.get_proof_ns env in
          (uu____121, uu____122) in
        FStar_Reflection_Basic.embed_pair
          (FStar_Reflection_Basic.embed_list
             FStar_Reflection_Basic.embed_binder
             FStar_Reflection_Data.fstar_refl_binder)
          FStar_Reflection_Data.fstar_refl_binders (embed_proof_namespace ps)
          fstar_tac_ns_typ uu____117 in
      FStar_Reflection_Basic.protect_embedded_term
        FStar_Reflection_Data.fstar_refl_env uu____116
let unembed_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun ps  ->
    fun protected_embedded_env  ->
      let embedded_env =
        FStar_Reflection_Basic.un_protect_embedded_term
          protected_embedded_env in
      let uu____131 =
        FStar_Reflection_Basic.unembed_pair
          (FStar_Reflection_Basic.unembed_list
             FStar_Reflection_Basic.unembed_binder)
          (unembed_proof_namespace ps) embedded_env in
      match uu____131 with
      | (binders,ns) ->
          let env = ps.FStar_Tactics_Basic.main_context in
          let env1 = FStar_TypeChecker_Env.set_proof_ns ns env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun b  ->
                   let uu____149 =
                     FStar_TypeChecker_Env.try_lookup_bv env2 (Prims.fst b) in
                   match uu____149 with
                   | None  -> FStar_TypeChecker_Env.push_binders env2 [b]
                   | uu____159 -> env2) env1 binders in
          env2
let embed_witness:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term Prims.option -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun w  ->
      FStar_Reflection_Basic.embed_option FStar_Reflection_Basic.embed_term
        FStar_Reflection_Data.fstar_refl_term w
let unembed_witness:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun t  ->
      FStar_Reflection_Basic.unembed_option
        FStar_Reflection_Basic.unembed_term t
let embed_goal:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Basic.goal -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun g  ->
      let uu____184 =
        pair_typ FStar_Reflection_Data.fstar_refl_env
          FStar_Reflection_Data.fstar_refl_term in
      FStar_Reflection_Basic.embed_pair
        (FStar_Reflection_Basic.embed_pair (embed_env ps)
           FStar_Reflection_Data.fstar_refl_env
           FStar_Reflection_Basic.embed_term
           FStar_Reflection_Data.fstar_refl_term) uu____184
        (embed_witness ps) FStar_Reflection_Data.fstar_refl_term
        (((g.FStar_Tactics_Basic.context), (g.FStar_Tactics_Basic.goal_ty)),
          (g.FStar_Tactics_Basic.witness))
let unembed_goal:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal
  =
  fun ps  ->
    fun t  ->
      let uu____197 =
        FStar_Reflection_Basic.unembed_pair
          (FStar_Reflection_Basic.unembed_pair (unembed_env ps)
             FStar_Reflection_Basic.unembed_term) (unembed_witness ps) t in
      match uu____197 with
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
      let uu____281 =
        let uu____282 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____283 =
          let uu____284 = FStar_Syntax_Syntax.iarg t_a in
          let uu____285 =
            let uu____287 =
              let uu____288 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____288 in
            let uu____289 =
              let uu____291 =
                let uu____292 =
                  embed_state ps1
                    ((ps1.FStar_Tactics_Basic.goals),
                      (ps1.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____292 in
              [uu____291] in
            uu____287 :: uu____289 in
          uu____284 :: uu____285 in
        FStar_Syntax_Syntax.mk_Tm_app uu____282 uu____283 in
      uu____281 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____301 =
        let uu____302 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____303 =
          let uu____304 = FStar_Syntax_Syntax.iarg t_a in
          let uu____305 =
            let uu____307 =
              let uu____308 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____308 in
            let uu____309 =
              let uu____311 =
                let uu____312 =
                  embed_state ps1
                    ((ps1.FStar_Tactics_Basic.goals),
                      (ps1.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____312 in
              [uu____311] in
            uu____307 :: uu____309 in
          uu____304 :: uu____305 in
        FStar_Syntax_Syntax.mk_Tm_app uu____302 uu____303 in
      uu____301 None FStar_Range.dummyRange
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____348 = FStar_Syntax_Util.head_and_args res1 in
  match uu____348 with
  | (hd1,args) ->
      let uu____380 =
        let uu____388 =
          let uu____389 = FStar_Syntax_Util.un_uinst hd1 in
          uu____389.FStar_Syntax_Syntax.n in
        (uu____388, args) in
      (match uu____380 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____406)::(embedded_state,uu____408)::[]) when
           let uu____442 = fstar_tactics_lid "Success" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____442 ->
           let uu____443 =
             let uu____446 = unembed_a a in
             let uu____447 = unembed_state ps embedded_state in
             (uu____446, uu____447) in
           FStar_Util.Inl uu____443
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____455)::(embedded_state,uu____457)::[])
           when
           let uu____491 = fstar_tactics_lid "Failed" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____491 ->
           let uu____492 =
             let uu____495 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____496 = unembed_state ps embedded_state in
             (uu____495, uu____496) in
           FStar_Util.Inr uu____492
       | uu____501 ->
           let uu____509 =
             let uu____510 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____510 in
           failwith uu____509)