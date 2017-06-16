open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid': Prims.string Prims.list -> FStar_Ident.lid =
  fun s  -> FStar_Syntax_Const.fstar_tactics_lid' s
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____9 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None in
    FStar_All.pipe_right uu____9 FStar_Syntax_Syntax.fv_to_tm
let mk_tactic_lid_as_term: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____13 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____13
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____17 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____17
let fstar_tactics_lid_as_data_tm: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____21 = fstar_tactics_lid' ["Effect"; s] in
    lid_as_data_tm uu____21
let fstar_tactics_Failed: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Failed"
let fstar_tactics_Success: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Success"
let pair_typ:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____30 =
        let uu____31 =
          let uu____32 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____32
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____33 =
          let uu____34 = FStar_Syntax_Syntax.as_arg t in
          let uu____35 =
            let uu____37 = FStar_Syntax_Syntax.as_arg s in [uu____37] in
          uu____34 :: uu____35 in
        FStar_Syntax_Syntax.mk_Tm_app uu____31 uu____33 in
      uu____30 None FStar_Range.dummyRange
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
      let uu____54 = FStar_Syntax_Util.un_alien t in
      FStar_All.pipe_right uu____54 FStar_Dyn.undyn
let embed_proofstate:
  FStar_Tactics_Basic.proofstate -> FStar_Syntax_Syntax.term =
  fun ps  -> FStar_Syntax_Util.mk_alien ps "tactics.embed_proofstate" None
let unembed_proofstate:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.proofstate
  =
  fun ps  ->
    fun t  ->
      let uu____64 = FStar_Syntax_Util.un_alien t in
      FStar_All.pipe_right uu____64 FStar_Dyn.undyn
let embed_result ps res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps1) ->
      let uu____96 =
        let uu____97 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____98 =
          let uu____99 = FStar_Syntax_Syntax.iarg t_a in
          let uu____100 =
            let uu____102 =
              let uu____103 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____103 in
            let uu____104 =
              let uu____106 =
                let uu____107 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____107 in
              [uu____106] in
            uu____102 :: uu____104 in
          uu____99 :: uu____100 in
        FStar_Syntax_Syntax.mk_Tm_app uu____97 uu____98 in
      uu____96 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____114 =
        let uu____115 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____116 =
          let uu____117 = FStar_Syntax_Syntax.iarg t_a in
          let uu____118 =
            let uu____120 =
              let uu____121 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____121 in
            let uu____122 =
              let uu____124 =
                let uu____125 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____125 in
              [uu____124] in
            uu____120 :: uu____122 in
          uu____117 :: uu____118 in
        FStar_Syntax_Syntax.mk_Tm_app uu____115 uu____116 in
      uu____114 None FStar_Range.dummyRange
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____159 = FStar_Syntax_Util.head_and_args res1 in
  match uu____159 with
  | (hd1,args) ->
      let uu____191 =
        let uu____199 =
          let uu____200 = FStar_Syntax_Util.un_uinst hd1 in
          uu____200.FStar_Syntax_Syntax.n in
        (uu____199, args) in
      (match uu____191 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____217)::(embedded_state,uu____219)::[]) when
           let uu____253 = fstar_tactics_lid' ["Effect"; "Success"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____253 ->
           let uu____254 =
             let uu____257 = unembed_a a in
             let uu____258 = unembed_proofstate ps embedded_state in
             (uu____257, uu____258) in
           FStar_Util.Inl uu____254
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____266)::(embedded_state,uu____268)::[])
           when
           let uu____302 = fstar_tactics_lid' ["Effect"; "Failed"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____302 ->
           let uu____303 =
             let uu____306 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____307 = unembed_proofstate ps embedded_state in
             (uu____306, uu____307) in
           FStar_Util.Inr uu____303
       | uu____312 ->
           let uu____320 =
             let uu____321 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____321 in
           failwith uu____320)