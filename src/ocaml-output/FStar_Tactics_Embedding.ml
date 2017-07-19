open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid': Prims.string Prims.list -> FStar_Ident.lid =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____13 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu____13 FStar_Syntax_Syntax.fv_to_tm
let mk_tactic_lid_as_term: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____18 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____18
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____23 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____23
let fstar_tactics_lid_as_data_tm: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____28 = fstar_tactics_lid' ["Effect"; s] in
    lid_as_data_tm uu____28
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
      let uu____41 =
        let uu____42 =
          let uu____43 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____43
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____44 =
          let uu____45 = FStar_Syntax_Syntax.as_arg t in
          let uu____46 =
            let uu____49 = FStar_Syntax_Syntax.as_arg s in [uu____49] in
          uu____45 :: uu____46 in
        FStar_Syntax_Syntax.mk_Tm_app uu____42 uu____44 in
      uu____41 FStar_Pervasives_Native.None FStar_Range.dummyRange
let embed_proofstate:
  FStar_Tactics_Basic.proofstate -> FStar_Syntax_Syntax.term =
  fun ps  ->
    FStar_Syntax_Util.mk_alien ps "tactics.embed_proofstate"
      FStar_Pervasives_Native.None
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
      let uu____103 =
        let uu____104 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____105 =
          let uu____106 = FStar_Syntax_Syntax.iarg t_a in
          let uu____107 =
            let uu____110 =
              let uu____111 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____111 in
            let uu____112 =
              let uu____115 =
                let uu____116 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____116 in
              [uu____115] in
            uu____110 :: uu____112 in
          uu____106 :: uu____107 in
        FStar_Syntax_Syntax.mk_Tm_app uu____104 uu____105 in
      uu____103 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____121 =
        let uu____122 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____123 =
          let uu____124 = FStar_Syntax_Syntax.iarg t_a in
          let uu____125 =
            let uu____128 =
              let uu____129 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____129 in
            let uu____130 =
              let uu____133 =
                let uu____134 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____134 in
              [uu____133] in
            uu____128 :: uu____130 in
          uu____124 :: uu____125 in
        FStar_Syntax_Syntax.mk_Tm_app uu____122 uu____123 in
      uu____121 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____176 = FStar_Syntax_Util.head_and_args res1 in
  match uu____176 with
  | (hd1,args) ->
      let uu____237 =
        let uu____252 =
          let uu____253 = FStar_Syntax_Util.un_uinst hd1 in
          uu____253.FStar_Syntax_Syntax.n in
        (uu____252, args) in
      (match uu____237 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____283)::(embedded_state,uu____285)::[]) when
           let uu____352 = fstar_tactics_lid' ["Effect"; "Success"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____352 ->
           let uu____353 =
             let uu____358 = unembed_a a in
             let uu____359 = unembed_proofstate ps embedded_state in
             (uu____358, uu____359) in
           FStar_Util.Inl uu____353
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____371)::(embedded_state,uu____373)::[])
           when
           let uu____440 = fstar_tactics_lid' ["Effect"; "Failed"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____440 ->
           let uu____441 =
             let uu____446 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____447 = unembed_proofstate ps embedded_state in
             (uu____446, uu____447) in
           FStar_Util.Inr uu____441
       | uu____456 ->
           let uu____471 =
             let uu____472 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____472 in
           failwith uu____471)