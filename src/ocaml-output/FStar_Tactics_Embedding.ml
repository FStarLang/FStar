open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid': Prims.string Prims.list -> FStar_Ident.lid =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____11 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu____11 FStar_Syntax_Syntax.fv_to_tm
let mk_tactic_lid_as_term: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____16 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____16
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____21 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____21
let fstar_tactics_lid_as_data_tm: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____26 = fstar_tactics_lid' ["Effect"; s] in
    lid_as_data_tm uu____26
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
      let uu____37 =
        let uu____38 =
          let uu____39 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____39
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____40 =
          let uu____41 = FStar_Syntax_Syntax.as_arg t in
          let uu____42 =
            let uu____44 = FStar_Syntax_Syntax.as_arg s in [uu____44] in
          uu____41 :: uu____42 in
        FStar_Syntax_Syntax.mk_Tm_app uu____38 uu____40 in
      uu____37 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
      let uu____61 = FStar_Syntax_Util.un_alien t in
      FStar_All.pipe_right uu____61 FStar_Dyn.undyn
let embed_result ps res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps1) ->
      let uu____98 =
        let uu____99 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____100 =
          let uu____101 = FStar_Syntax_Syntax.iarg t_a in
          let uu____102 =
            let uu____104 =
              let uu____105 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____105 in
            let uu____106 =
              let uu____108 =
                let uu____109 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____109 in
              [uu____108] in
            uu____104 :: uu____106 in
          uu____101 :: uu____102 in
        FStar_Syntax_Syntax.mk_Tm_app uu____99 uu____100 in
      uu____98 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____116 =
        let uu____117 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____118 =
          let uu____119 = FStar_Syntax_Syntax.iarg t_a in
          let uu____120 =
            let uu____122 =
              let uu____123 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____123 in
            let uu____124 =
              let uu____126 =
                let uu____127 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____127 in
              [uu____126] in
            uu____122 :: uu____124 in
          uu____119 :: uu____120 in
        FStar_Syntax_Syntax.mk_Tm_app uu____117 uu____118 in
      uu____116 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____165 = FStar_Syntax_Util.head_and_args res1 in
  match uu____165 with
  | (hd1,args) ->
      let uu____197 =
        let uu____205 =
          let uu____206 = FStar_Syntax_Util.un_uinst hd1 in
          uu____206.FStar_Syntax_Syntax.n in
        (uu____205, args) in
      (match uu____197 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____223)::(embedded_state,uu____225)::[]) when
           let uu____259 = fstar_tactics_lid' ["Effect"; "Success"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____259 ->
           let uu____260 =
             let uu____263 = unembed_a a in
             let uu____264 = unembed_proofstate ps embedded_state in
             (uu____263, uu____264) in
           FStar_Util.Inl uu____260
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____272)::(embedded_state,uu____274)::[])
           when
           let uu____308 = fstar_tactics_lid' ["Effect"; "Failed"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____308 ->
           let uu____309 =
             let uu____312 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____313 = unembed_proofstate ps embedded_state in
             (uu____312, uu____313) in
           FStar_Util.Inr uu____309
       | uu____318 ->
           let uu____326 =
             let uu____327 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____327 in
           failwith uu____326)