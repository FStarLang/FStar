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
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____39 =
        let uu____40 =
          let uu____41 = lid_as_tm FStar_Parser_Const.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____41
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____42 =
          let uu____43 = FStar_Syntax_Syntax.as_arg t in
          let uu____44 =
            let uu____47 = FStar_Syntax_Syntax.as_arg s in [uu____47] in
          uu____43 :: uu____44 in
        FStar_Syntax_Syntax.mk_Tm_app uu____40 uu____42 in
      uu____39 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
      let uu____62 = FStar_Syntax_Util.un_alien t in
      FStar_All.pipe_right uu____62 FStar_Dyn.undyn
let embed_result:
  'a .
    FStar_Tactics_Basic.proofstate ->
      'a FStar_Tactics_Basic.result ->
        ('a -> FStar_Syntax_Syntax.term) ->
          FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun res  ->
      fun embed_a  ->
        fun t_a  ->
          match res with
          | FStar_Tactics_Basic.Failed (msg,ps1) ->
              let uu____101 =
                let uu____102 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____103 =
                  let uu____104 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____105 =
                    let uu____108 =
                      let uu____109 =
                        FStar_Syntax_Embeddings.embed_string msg in
                      FStar_Syntax_Syntax.as_arg uu____109 in
                    let uu____110 =
                      let uu____113 =
                        let uu____114 = embed_proofstate ps1 in
                        FStar_Syntax_Syntax.as_arg uu____114 in
                      [uu____113] in
                    uu____108 :: uu____110 in
                  uu____104 :: uu____105 in
                FStar_Syntax_Syntax.mk_Tm_app uu____102 uu____103 in
              uu____101 FStar_Pervasives_Native.None FStar_Range.dummyRange
          | FStar_Tactics_Basic.Success (a,ps1) ->
              let uu____119 =
                let uu____120 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____121 =
                  let uu____122 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____123 =
                    let uu____126 =
                      let uu____127 = embed_a a in
                      FStar_Syntax_Syntax.as_arg uu____127 in
                    let uu____128 =
                      let uu____131 =
                        let uu____132 = embed_proofstate ps1 in
                        FStar_Syntax_Syntax.as_arg uu____132 in
                      [uu____131] in
                    uu____126 :: uu____128 in
                  uu____122 :: uu____123 in
                FStar_Syntax_Syntax.mk_Tm_app uu____120 uu____121 in
              uu____119 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_result:
  'a .
    FStar_Tactics_Basic.proofstate ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term -> 'a) ->
          (('a,FStar_Tactics_Basic.proofstate) FStar_Pervasives_Native.tuple2,
            (Prims.string,FStar_Tactics_Basic.proofstate)
              FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun ps  ->
    fun res  ->
      fun unembed_a  ->
        let res1 = FStar_Syntax_Util.unascribe res in
        let uu____174 = FStar_Syntax_Util.head_and_args res1 in
        match uu____174 with
        | (hd1,args) ->
            let uu____223 =
              let uu____236 =
                let uu____237 = FStar_Syntax_Util.un_uinst hd1 in
                uu____237.FStar_Syntax_Syntax.n in
              (uu____236, args) in
            (match uu____223 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,_t::(a,uu____263)::(embedded_state,uu____265)::[]) when
                 let uu____312 = fstar_tactics_lid' ["Effect"; "Success"] in
                 FStar_Syntax_Syntax.fv_eq_lid fv uu____312 ->
                 let uu____313 =
                   let uu____318 = unembed_a a in
                   let uu____319 = unembed_proofstate ps embedded_state in
                   (uu____318, uu____319) in
                 FStar_Util.Inl uu____313
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,_t::(embedded_string,uu____331)::(embedded_state,uu____333)::[])
                 when
                 let uu____380 = fstar_tactics_lid' ["Effect"; "Failed"] in
                 FStar_Syntax_Syntax.fv_eq_lid fv uu____380 ->
                 let uu____381 =
                   let uu____386 =
                     FStar_Syntax_Embeddings.unembed_string embedded_string in
                   let uu____387 = unembed_proofstate ps embedded_state in
                   (uu____386, uu____387) in
                 FStar_Util.Inr uu____381
             | uu____396 ->
                 let uu____409 =
                   let uu____410 = FStar_Syntax_Print.term_to_string res1 in
                   FStar_Util.format1 "Not an embedded result: %s" uu____410 in
                 failwith uu____409)