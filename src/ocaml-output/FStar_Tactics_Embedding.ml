open Prims
type name = FStar_Syntax_Syntax.bv[@@deriving show]
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
let fstar_tactics_Failed_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Result"; "Failed"]
let fstar_tactics_Success_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Result"; "Success"]
let fstar_tactics_Failed_tm: FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Failed_lid
let fstar_tactics_Success_tm: FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Success_lid
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
  FStar_Tactics_Types.proofstate -> FStar_Syntax_Syntax.term =
  fun ps  ->
    FStar_Syntax_Util.mk_alien ps "tactics.embed_proofstate"
      FStar_Pervasives_Native.None
let unembed_proofstate:
  FStar_Syntax_Syntax.term -> FStar_Tactics_Types.proofstate =
  fun t  ->
    let uu____58 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____58 FStar_Dyn.undyn
let mk_app:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun hd1  ->
    fun args  ->
      FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
        FStar_Range.dummyRange
let mktuple2_tm: FStar_Syntax_Syntax.term =
  lid_as_data_tm FStar_Parser_Const.lid_Mktuple2
let t_proofstate: FStar_Syntax_Syntax.term =
  let uu____69 = fstar_tactics_lid' ["Types"; "proofstate"] in
  FStar_Syntax_Syntax.tconst uu____69
let embed_result:
  'a .
    FStar_Tactics_Types.proofstate ->
      'a FStar_Tactics_Result.__result ->
        ('a -> FStar_Syntax_Syntax.term) ->
          FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun res  ->
      fun embed_a  ->
        fun t_a  ->
          match res with
          | FStar_Tactics_Result.Failed (msg,ps1) ->
              let uu____108 =
                FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____109 =
                let uu____110 = FStar_Syntax_Syntax.iarg t_a in
                let uu____111 =
                  let uu____114 =
                    let uu____115 =
                      let uu____116 =
                        FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                          [FStar_Syntax_Syntax.U_zero;
                          FStar_Syntax_Syntax.U_zero] in
                      let uu____117 =
                        let uu____118 =
                          FStar_Syntax_Syntax.iarg
                            FStar_Syntax_Syntax.t_string in
                        let uu____119 =
                          let uu____122 =
                            FStar_Syntax_Syntax.iarg t_proofstate in
                          let uu____123 =
                            let uu____126 =
                              let uu____127 =
                                FStar_Syntax_Embeddings.embed_string msg in
                              FStar_Syntax_Syntax.as_arg uu____127 in
                            let uu____128 =
                              let uu____131 =
                                let uu____132 = embed_proofstate ps1 in
                                FStar_Syntax_Syntax.as_arg uu____132 in
                              [uu____131] in
                            uu____126 :: uu____128 in
                          uu____122 :: uu____123 in
                        uu____118 :: uu____119 in
                      mk_app uu____116 uu____117 in
                    FStar_Syntax_Syntax.as_arg uu____115 in
                  [uu____114] in
                uu____110 :: uu____111 in
              mk_app uu____108 uu____109
          | FStar_Tactics_Result.Success (a,ps1) ->
              let uu____135 =
                FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____136 =
                let uu____137 = FStar_Syntax_Syntax.iarg t_a in
                let uu____138 =
                  let uu____141 =
                    let uu____142 =
                      let uu____143 =
                        FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                          [FStar_Syntax_Syntax.U_zero;
                          FStar_Syntax_Syntax.U_zero] in
                      let uu____144 =
                        let uu____145 = FStar_Syntax_Syntax.iarg t_a in
                        let uu____146 =
                          let uu____149 =
                            FStar_Syntax_Syntax.iarg t_proofstate in
                          let uu____150 =
                            let uu____153 =
                              let uu____154 = embed_a a in
                              FStar_Syntax_Syntax.as_arg uu____154 in
                            let uu____155 =
                              let uu____158 =
                                let uu____159 = embed_proofstate ps1 in
                                FStar_Syntax_Syntax.as_arg uu____159 in
                              [uu____158] in
                            uu____153 :: uu____155 in
                          uu____149 :: uu____150 in
                        uu____145 :: uu____146 in
                      mk_app uu____143 uu____144 in
                    FStar_Syntax_Syntax.as_arg uu____142 in
                  [uu____141] in
                uu____137 :: uu____138 in
              mk_app uu____135 uu____136
let unembed_result:
  'a .
    FStar_Tactics_Types.proofstate ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term -> 'a) ->
          (('a,FStar_Tactics_Types.proofstate) FStar_Pervasives_Native.tuple2,
            (Prims.string,FStar_Tactics_Types.proofstate)
              FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun ps  ->
    fun res  ->
      fun unembed_a  ->
        let hd'_and_args tm =
          let tm1 = FStar_Syntax_Util.unascribe tm in
          let uu____215 = FStar_Syntax_Util.head_and_args tm1 in
          match uu____215 with
          | (hd1,args) ->
              let uu____264 =
                let uu____265 = FStar_Syntax_Util.un_uinst hd1 in
                uu____265.FStar_Syntax_Syntax.n in
              (uu____264, args) in
        let tuple2_elements tm =
          let uu____288 = hd'_and_args tm in
          match uu____288 with
          | (FStar_Syntax_Syntax.Tm_fvar
             fv,_t1::_t2::(arg1,uu____313)::(arg2,uu____315)::[]) when
              FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.lid_Mktuple2
              -> (arg1, arg2)
          | uu____378 ->
              let uu____391 =
                let uu____392 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.format1 "Expected a two-elements tuple, got %s"
                  uu____392 in
              failwith uu____391 in
        let uu____401 = hd'_and_args res in
        match uu____401 with
        | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____429)::[]) when
            FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
            let uu____466 = tuple2_elements tuple2 in
            (match uu____466 with
             | (embedded_a,embedded_ps) ->
                 let uu____497 =
                   let uu____502 = unembed_a embedded_a in
                   let uu____503 = unembed_proofstate embedded_ps in
                   (uu____502, uu____503) in
                 FStar_Util.Inl uu____497)
        | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____515)::[]) when
            FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
            let uu____552 = tuple2_elements tuple2 in
            (match uu____552 with
             | (embedded_msg,embedded_ps) ->
                 let uu____583 =
                   let uu____588 =
                     FStar_Syntax_Embeddings.unembed_string embedded_msg in
                   let uu____589 = unembed_proofstate embedded_ps in
                   (uu____588, uu____589) in
                 FStar_Util.Inr uu____583)
        | uu____598 ->
            let uu____611 =
              let uu____612 = FStar_Syntax_Print.term_to_string res in
              FStar_Util.format1
                "Expected Result.Success or Result.Failed applied to a single argument, got %s"
                uu____612 in
            failwith uu____611