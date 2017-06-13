open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid': Prims.string Prims.list -> FStar_Ident.lid =
  fun s  -> FStar_Syntax_Const.fstar_tactics_lid' s
let fstar_tactics_lid: Prims.string -> FStar_Ident.lid =
  fun s  -> FStar_Syntax_Const.fstar_tactics_lid s
let by_tactic_lid: FStar_Ident.lid = FStar_Syntax_Const.by_tactic_lid
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____15 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None in
    FStar_All.pipe_right uu____15 FStar_Syntax_Syntax.fv_to_tm
let mk_tactic_lid_as_term: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____20 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____20
let fstar_tactics_goal: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goal"
let fstar_tactics_goals: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goals"
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____25 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____25
let fstar_tactics_lid_as_data_tm: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____30 = fstar_tactics_lid' ["Effect"; s] in
    lid_as_data_tm uu____30
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
  let uu____37 =
    let uu____38 =
      let uu____39 = lid_as_tm FStar_Syntax_Const.list_lid in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____39 [FStar_Syntax_Syntax.U_zero] in
    let uu____40 =
      let uu____41 = FStar_Syntax_Syntax.as_arg t_string in [uu____41] in
    FStar_Syntax_Syntax.mk_Tm_app uu____38 uu____40 in
  uu____37 None FStar_Range.dummyRange
let pair_typ:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____56 =
        let uu____57 =
          let uu____58 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____58
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____59 =
          let uu____60 = FStar_Syntax_Syntax.as_arg t in
          let uu____61 =
            let uu____63 = FStar_Syntax_Syntax.as_arg s in [uu____63] in
          uu____60 :: uu____61 in
        FStar_Syntax_Syntax.mk_Tm_app uu____57 uu____59 in
      uu____56 None FStar_Range.dummyRange
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
      let uu____97 = FStar_List.hd ns in
      FStar_Reflection_Basic.embed_list embed_elt fstar_tac_nselt_typ
        uu____97
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
      let uu____135 =
        let uu____136 =
          let uu____140 = FStar_TypeChecker_Env.all_binders env in
          let uu____141 = FStar_TypeChecker_Env.get_proof_ns env in
          (uu____140, uu____141) in
        FStar_Reflection_Basic.embed_pair
          (FStar_Reflection_Basic.embed_list
             FStar_Reflection_Basic.embed_binder
             FStar_Reflection_Data.fstar_refl_binder)
          FStar_Reflection_Data.fstar_refl_binders (embed_proof_namespace ps)
          fstar_tac_ns_typ uu____136 in
      FStar_Reflection_Basic.protect_embedded_term
        FStar_Reflection_Data.fstar_refl_env uu____135
let unembed_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun ps  ->
    fun protected_embedded_env  ->
      let embedded_env =
        FStar_Reflection_Basic.un_protect_embedded_term
          protected_embedded_env in
      let uu____152 =
        FStar_Reflection_Basic.unembed_pair
          (FStar_Reflection_Basic.unembed_list
             FStar_Reflection_Basic.unembed_binder)
          (unembed_proof_namespace ps) embedded_env in
      match uu____152 with
      | (binders,ns) ->
          let env = ps.FStar_Tactics_Basic.main_context in
          let env1 = FStar_TypeChecker_Env.set_proof_ns ns env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun b  ->
                   let uu____170 =
                     FStar_TypeChecker_Env.try_lookup_bv env2 (fst b) in
                   match uu____170 with
                   | None  -> FStar_TypeChecker_Env.push_binders env2 [b]
                   | uu____180 -> env2) env1 binders in
          env2
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
      let uu____208 =
        pair_typ FStar_Reflection_Data.fstar_refl_env
          FStar_Reflection_Data.fstar_refl_term in
      FStar_Reflection_Basic.embed_pair
        (FStar_Reflection_Basic.embed_pair (embed_env ps)
           FStar_Reflection_Data.fstar_refl_env
           FStar_Reflection_Basic.embed_term
           FStar_Reflection_Data.fstar_refl_term) uu____208
        (embed_witness ps) FStar_Reflection_Data.fstar_refl_term
        (((g.FStar_Tactics_Basic.context), (g.FStar_Tactics_Basic.goal_ty)),
          (g.FStar_Tactics_Basic.witness))
let unembed_goal:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal
  =
  fun ps  ->
    fun t  ->
      let uu____221 =
        FStar_Reflection_Basic.unembed_pair
          (FStar_Reflection_Basic.unembed_pair (unembed_env ps)
             FStar_Reflection_Basic.unembed_term) (unembed_witness ps) t in
      match uu____221 with
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
      let uu____314 =
        let uu____315 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____316 =
          let uu____317 = FStar_Syntax_Syntax.iarg t_a in
          let uu____318 =
            let uu____320 =
              let uu____321 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____321 in
            let uu____322 =
              let uu____324 =
                let uu____325 =
                  embed_state ps1
                    ((ps1.FStar_Tactics_Basic.goals),
                      (ps1.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____325 in
              [uu____324] in
            uu____320 :: uu____322 in
          uu____317 :: uu____318 in
        FStar_Syntax_Syntax.mk_Tm_app uu____315 uu____316 in
      uu____314 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____334 =
        let uu____335 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____336 =
          let uu____337 = FStar_Syntax_Syntax.iarg t_a in
          let uu____338 =
            let uu____340 =
              let uu____341 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____341 in
            let uu____342 =
              let uu____344 =
                let uu____345 =
                  embed_state ps1
                    ((ps1.FStar_Tactics_Basic.goals),
                      (ps1.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____345 in
              [uu____344] in
            uu____340 :: uu____342 in
          uu____337 :: uu____338 in
        FStar_Syntax_Syntax.mk_Tm_app uu____335 uu____336 in
      uu____334 None FStar_Range.dummyRange
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____385 = FStar_Syntax_Util.head_and_args res1 in
  match uu____385 with
  | (hd1,args) ->
      let uu____417 =
        let uu____425 =
          let uu____426 = FStar_Syntax_Util.un_uinst hd1 in
          uu____426.FStar_Syntax_Syntax.n in
        (uu____425, args) in
      (match uu____417 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____443)::(embedded_state,uu____445)::[]) when
           let uu____479 = fstar_tactics_lid' ["Effect"; "Success"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____479 ->
           let uu____480 =
             let uu____483 = unembed_a a in
             let uu____484 = unembed_state ps embedded_state in
             (uu____483, uu____484) in
           FStar_Util.Inl uu____480
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____492)::(embedded_state,uu____494)::[])
           when
           let uu____528 = fstar_tactics_lid' ["Effect"; "Failed"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____528 ->
           let uu____529 =
             let uu____532 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____533 = unembed_state ps embedded_state in
             (uu____532, uu____533) in
           FStar_Util.Inr uu____529
       | uu____538 ->
           let uu____546 =
             let uu____547 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____547 in
           failwith uu____546)