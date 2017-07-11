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
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____36 =
        let uu____37 =
          let uu____38 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____38
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____39 =
          let uu____40 = FStar_Syntax_Syntax.as_arg t in
          let uu____41 =
            let uu____43 = FStar_Syntax_Syntax.as_arg s in [uu____43] in
          uu____40 :: uu____41 in
        FStar_Syntax_Syntax.mk_Tm_app uu____37 uu____39 in
      uu____36 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
      let uu____60 = FStar_Syntax_Util.un_alien t in
      FStar_All.pipe_right uu____60 FStar_Dyn.undyn
let embed_result ps res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps1) ->
      let uu____97 =
        let uu____98 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____99 =
          let uu____100 = FStar_Syntax_Syntax.iarg t_a in
          let uu____101 =
            let uu____103 =
              let uu____104 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____104 in
            let uu____105 =
              let uu____107 =
                let uu____108 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____108 in
              [uu____107] in
            uu____103 :: uu____105 in
          uu____100 :: uu____101 in
        FStar_Syntax_Syntax.mk_Tm_app uu____98 uu____99 in
      uu____97 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____115 =
        let uu____116 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____117 =
          let uu____118 = FStar_Syntax_Syntax.iarg t_a in
          let uu____119 =
            let uu____121 =
              let uu____122 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____122 in
            let uu____123 =
              let uu____125 =
                let uu____126 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____126 in
              [uu____125] in
            uu____121 :: uu____123 in
          uu____118 :: uu____119 in
        FStar_Syntax_Syntax.mk_Tm_app uu____116 uu____117 in
      uu____115 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____164 = FStar_Syntax_Util.head_and_args res1 in
  match uu____164 with
  | (hd1,args) ->
      let uu____190 =
        let uu____197 =
          let uu____198 = FStar_Syntax_Util.un_uinst hd1 in
          uu____198.FStar_Syntax_Syntax.n in
        (uu____197, args) in
      (match uu____190 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____213)::(embedded_state,uu____215)::[]) when
           let uu____239 = fstar_tactics_lid' ["Effect"; "Success"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____239 ->
           let uu____240 =
             let uu____243 = unembed_a a in
             let uu____244 = unembed_proofstate ps embedded_state in
             (uu____243, uu____244) in
           FStar_Util.Inl uu____240
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____252)::(embedded_state,uu____254)::[])
           when
           let uu____278 = fstar_tactics_lid' ["Effect"; "Failed"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____278 ->
           let uu____279 =
             let uu____282 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____283 = unembed_proofstate ps embedded_state in
             (uu____282, uu____283) in
           FStar_Util.Inr uu____279
       | uu____288 ->
           let uu____295 =
             let uu____296 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____296 in
           failwith uu____295)