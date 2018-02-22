open Prims
type name = FStar_Syntax_Syntax.bv[@@deriving show]
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
    let uu____15 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____15
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____19 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____19
let fstar_tactics_lid_as_data_tm: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____23 = fstar_tactics_lid' ["Effect"; s] in
    lid_as_data_tm uu____23
let fstar_tactics_Failed_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Result"; "Failed"]
let fstar_tactics_Success_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Result"; "Success"]
let fstar_tactics_Failed_tm: FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Failed_lid
let fstar_tactics_Success_tm: FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_Success_lid
let fstar_tactics_topdown_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Types"; "TopDown"]
let fstar_tactics_bottomup_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Types"; "BottomUp"]
let fstar_tactics_topdown: FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_topdown_lid
let fstar_tactics_bottomup: FStar_Syntax_Syntax.term =
  lid_as_data_tm fstar_tactics_bottomup_lid
let mktuple2_tm: FStar_Syntax_Syntax.term =
  lid_as_data_tm FStar_Parser_Const.lid_Mktuple2
let t_proofstate: FStar_Syntax_Syntax.term =
  let uu____24 = fstar_tactics_lid' ["Types"; "proofstate"] in
  FStar_Syntax_Syntax.tconst uu____24
let pair_typ:
  FStar_Reflection_Data.typ ->
    FStar_Reflection_Data.typ -> FStar_Reflection_Data.typ
  =
  fun t  ->
    fun s  ->
      let uu____31 =
        let uu____32 =
          let uu____33 = lid_as_tm FStar_Parser_Const.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____33
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____34 =
          let uu____35 = FStar_Syntax_Syntax.as_arg t in
          let uu____36 =
            let uu____39 = FStar_Syntax_Syntax.as_arg s in [uu____39] in
          uu____35 :: uu____36 in
        FStar_Syntax_Syntax.mk_Tm_app uu____32 uu____34 in
      uu____31 FStar_Pervasives_Native.None FStar_Range.dummyRange
let embed_proofstate:
  FStar_Range.range ->
    FStar_Tactics_Types.proofstate -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun ps  ->
      FStar_Syntax_Util.mk_alien t_proofstate ps "tactics.embed_proofstate"
        (FStar_Pervasives_Native.Some rng)
let unembed_proofstate:
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.proofstate FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____67 =
        let uu____68 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____68 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____67
    with
    | uu____75 ->
        ((let uu____77 =
            let uu____82 =
              let uu____83 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded proofstate: %s" uu____83 in
            (FStar_Errors.Warning_NotEmbedded, uu____82) in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____77);
         FStar_Pervasives_Native.None)
let embed_result:
  'a .
    'a FStar_Syntax_Embeddings.embedder ->
      FStar_Reflection_Data.typ ->
        'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedder
  =
  fun embed_a  ->
    fun t_a  ->
      fun rng  ->
        fun res  ->
          match res with
          | FStar_Tactics_Result.Failed (msg,ps) ->
              let uu____127 =
                let uu____128 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____129 =
                  let uu____130 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____131 =
                    let uu____134 =
                      let uu____135 =
                        let uu____136 =
                          let uu____137 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero] in
                          let uu____138 =
                            let uu____139 =
                              FStar_Syntax_Syntax.iarg
                                FStar_Syntax_Syntax.t_string in
                            let uu____140 =
                              let uu____143 =
                                FStar_Syntax_Syntax.iarg t_proofstate in
                              let uu____144 =
                                let uu____147 =
                                  let uu____148 =
                                    FStar_Syntax_Embeddings.embed_string rng
                                      msg in
                                  FStar_Syntax_Syntax.as_arg uu____148 in
                                let uu____149 =
                                  let uu____152 =
                                    let uu____153 = embed_proofstate rng ps in
                                    FStar_Syntax_Syntax.as_arg uu____153 in
                                  [uu____152] in
                                uu____147 :: uu____149 in
                              uu____143 :: uu____144 in
                            uu____139 :: uu____140 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____137 uu____138 in
                        uu____136 FStar_Pervasives_Native.None rng in
                      FStar_Syntax_Syntax.as_arg uu____135 in
                    [uu____134] in
                  uu____130 :: uu____131 in
                FStar_Syntax_Syntax.mk_Tm_app uu____128 uu____129 in
              uu____127 FStar_Pervasives_Native.None rng
          | FStar_Tactics_Result.Success (a,ps) ->
              let uu____160 =
                let uu____161 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____162 =
                  let uu____163 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____164 =
                    let uu____167 =
                      let uu____168 =
                        let uu____169 =
                          let uu____170 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero] in
                          let uu____171 =
                            let uu____172 = FStar_Syntax_Syntax.iarg t_a in
                            let uu____173 =
                              let uu____176 =
                                FStar_Syntax_Syntax.iarg t_proofstate in
                              let uu____177 =
                                let uu____180 =
                                  let uu____181 = embed_a rng a in
                                  FStar_Syntax_Syntax.as_arg uu____181 in
                                let uu____185 =
                                  let uu____188 =
                                    let uu____189 = embed_proofstate rng ps in
                                    FStar_Syntax_Syntax.as_arg uu____189 in
                                  [uu____188] in
                                uu____180 :: uu____185 in
                              uu____176 :: uu____177 in
                            uu____172 :: uu____173 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____170 uu____171 in
                        uu____169 FStar_Pervasives_Native.None rng in
                      FStar_Syntax_Syntax.as_arg uu____168 in
                    [uu____167] in
                  uu____163 :: uu____164 in
                FStar_Syntax_Syntax.mk_Tm_app uu____161 uu____162 in
              uu____160 FStar_Pervasives_Native.None rng
let unembed_result:
  'a .
    FStar_Syntax_Syntax.term ->
      'a FStar_Syntax_Embeddings.unembedder ->
        (('a,FStar_Tactics_Types.proofstate) FStar_Pervasives_Native.tuple2,
          (Prims.string,FStar_Tactics_Types.proofstate)
            FStar_Pervasives_Native.tuple2)
          FStar_Util.either FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm in
        let uu____245 = FStar_Syntax_Util.head_and_args tm1 in
        match uu____245 with
        | (hd1,args) ->
            let uu____294 =
              let uu____295 = FStar_Syntax_Util.un_uinst hd1 in
              uu____295.FStar_Syntax_Syntax.n in
            (uu____294, args) in
      let uu____306 = hd'_and_args t in
      match uu____306 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____336)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____373 =
            let uu____380 =
              FStar_Syntax_Embeddings.unembed_pair unembed_a
                unembed_proofstate in
            uu____380 tuple2 in
          FStar_Util.bind_opt uu____373
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inl x))
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____438)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____475 =
            let uu____482 =
              FStar_Syntax_Embeddings.unembed_pair
                FStar_Syntax_Embeddings.unembed_string unembed_proofstate in
            uu____482 tuple2 in
          FStar_Util.bind_opt uu____475
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inr x))
      | uu____533 ->
          ((let uu____547 =
              let uu____552 =
                let uu____553 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded tactic result: %s"
                  uu____553 in
              (FStar_Errors.Warning_NotEmbedded, uu____552) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____547);
           FStar_Pervasives_Native.None)
let embed_direction:
  FStar_Range.range ->
    FStar_Tactics_Types.direction -> FStar_Syntax_Syntax.term
  =
  fun rng  ->
    fun d  ->
      match d with
      | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
      | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup
let unembed_direction:
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.direction FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____584 =
      let uu____585 = FStar_Syntax_Subst.compress t in
      uu____585.FStar_Syntax_Syntax.n in
    match uu____584 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____592 ->
        ((let uu____594 =
            let uu____599 =
              let uu____600 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded direction: %s" uu____600 in
            (FStar_Errors.Warning_NotEmbedded, uu____599) in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____594);
         FStar_Pervasives_Native.None)