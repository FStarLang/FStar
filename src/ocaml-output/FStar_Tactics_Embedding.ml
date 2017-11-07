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
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____33 =
        let uu____34 =
          let uu____35 = lid_as_tm FStar_Parser_Const.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____35
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____36 =
          let uu____37 = FStar_Syntax_Syntax.as_arg t in
          let uu____38 =
            let uu____41 = FStar_Syntax_Syntax.as_arg s in [uu____41] in
          uu____37 :: uu____38 in
        FStar_Syntax_Syntax.mk_Tm_app uu____34 uu____36 in
      uu____33 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
      let uu____64 =
        let uu____65 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____65 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____64
    with
    | uu____72 ->
        ((let uu____74 =
            let uu____75 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded proofstate: %s" uu____75 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____74);
         FStar_Pervasives_Native.None)
let embed_result:
  'a .
    'a FStar_Syntax_Embeddings.embedder ->
      FStar_Reflection_Data.typ ->
        FStar_Range.range ->
          'a FStar_Tactics_Result.__result -> FStar_Syntax_Syntax.term
  =
  fun embed_a  ->
    fun t_a  ->
      fun rng  ->
        fun res  ->
          match res with
          | FStar_Tactics_Result.Failed (msg,ps) ->
              let uu____117 =
                let uu____118 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____119 =
                  let uu____120 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____121 =
                    let uu____124 =
                      let uu____125 =
                        let uu____126 =
                          let uu____127 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero] in
                          let uu____128 =
                            let uu____129 =
                              FStar_Syntax_Syntax.iarg
                                FStar_Syntax_Syntax.t_string in
                            let uu____130 =
                              let uu____133 =
                                FStar_Syntax_Syntax.iarg t_proofstate in
                              let uu____134 =
                                let uu____137 =
                                  let uu____138 =
                                    FStar_Syntax_Embeddings.embed_string rng
                                      msg in
                                  FStar_Syntax_Syntax.as_arg uu____138 in
                                let uu____139 =
                                  let uu____142 =
                                    let uu____143 = embed_proofstate rng ps in
                                    FStar_Syntax_Syntax.as_arg uu____143 in
                                  [uu____142] in
                                uu____137 :: uu____139 in
                              uu____133 :: uu____134 in
                            uu____129 :: uu____130 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____127 uu____128 in
                        uu____126 FStar_Pervasives_Native.None rng in
                      FStar_Syntax_Syntax.as_arg uu____125 in
                    [uu____124] in
                  uu____120 :: uu____121 in
                FStar_Syntax_Syntax.mk_Tm_app uu____118 uu____119 in
              uu____117 FStar_Pervasives_Native.None rng
          | FStar_Tactics_Result.Success (a,ps) ->
              let uu____150 =
                let uu____151 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____152 =
                  let uu____153 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____154 =
                    let uu____157 =
                      let uu____158 =
                        let uu____159 =
                          let uu____160 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero] in
                          let uu____161 =
                            let uu____162 = FStar_Syntax_Syntax.iarg t_a in
                            let uu____163 =
                              let uu____166 =
                                FStar_Syntax_Syntax.iarg t_proofstate in
                              let uu____167 =
                                let uu____170 =
                                  let uu____171 = embed_a rng a in
                                  FStar_Syntax_Syntax.as_arg uu____171 in
                                let uu____175 =
                                  let uu____178 =
                                    let uu____179 = embed_proofstate rng ps in
                                    FStar_Syntax_Syntax.as_arg uu____179 in
                                  [uu____178] in
                                uu____170 :: uu____175 in
                              uu____166 :: uu____167 in
                            uu____162 :: uu____163 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____160 uu____161 in
                        uu____159 FStar_Pervasives_Native.None rng in
                      FStar_Syntax_Syntax.as_arg uu____158 in
                    [uu____157] in
                  uu____153 :: uu____154 in
                FStar_Syntax_Syntax.mk_Tm_app uu____151 uu____152 in
              uu____150 FStar_Pervasives_Native.None rng
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
        let uu____235 = FStar_Syntax_Util.head_and_args tm1 in
        match uu____235 with
        | (hd1,args) ->
            let uu____284 =
              let uu____285 = FStar_Syntax_Util.un_uinst hd1 in
              uu____285.FStar_Syntax_Syntax.n in
            (uu____284, args) in
      let uu____296 = hd'_and_args t in
      match uu____296 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____326)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____363 =
            let uu____370 =
              FStar_Syntax_Embeddings.unembed_pair unembed_a
                unembed_proofstate in
            uu____370 tuple2 in
          FStar_Util.bind_opt uu____363
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inl x))
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____428)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____465 =
            let uu____472 =
              FStar_Syntax_Embeddings.unembed_pair
                FStar_Syntax_Embeddings.unembed_string unembed_proofstate in
            uu____472 tuple2 in
          FStar_Util.bind_opt uu____465
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inr x))
      | uu____523 ->
          ((let uu____537 =
              let uu____538 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded tactic result: %s"
                uu____538 in
            FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____537);
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
    let uu____564 =
      let uu____565 = FStar_Syntax_Subst.compress t in
      uu____565.FStar_Syntax_Syntax.n in
    match uu____564 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____572 ->
        ((let uu____574 =
            let uu____575 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded direction: %s" uu____575 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____574);
         FStar_Pervasives_Native.None)