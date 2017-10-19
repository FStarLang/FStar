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
  let uu____29 = fstar_tactics_lid' ["Types"; "proofstate"] in
  FStar_Syntax_Syntax.tconst uu____29
let pair_typ:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____40 =
        let uu____41 =
          let uu____42 = lid_as_tm FStar_Parser_Const.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____42
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____43 =
          let uu____44 = FStar_Syntax_Syntax.as_arg t in
          let uu____45 =
            let uu____48 = FStar_Syntax_Syntax.as_arg s in [uu____48] in
          uu____44 :: uu____45 in
        FStar_Syntax_Syntax.mk_Tm_app uu____41 uu____43 in
      uu____40 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
      let uu____74 =
        let uu____75 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____75 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____74
    with
    | uu____82 ->
        ((let uu____84 =
            let uu____85 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded proofstate: %s" uu____85 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____84);
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
              let uu____132 =
                let uu____133 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____134 =
                  let uu____135 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____136 =
                    let uu____139 =
                      let uu____140 =
                        let uu____141 =
                          let uu____142 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero] in
                          let uu____143 =
                            let uu____144 =
                              FStar_Syntax_Syntax.iarg
                                FStar_Syntax_Syntax.t_string in
                            let uu____145 =
                              let uu____148 =
                                FStar_Syntax_Syntax.iarg t_proofstate in
                              let uu____149 =
                                let uu____152 =
                                  let uu____153 =
                                    FStar_Syntax_Embeddings.embed_string rng
                                      msg in
                                  FStar_Syntax_Syntax.as_arg uu____153 in
                                let uu____154 =
                                  let uu____157 =
                                    let uu____158 = embed_proofstate rng ps in
                                    FStar_Syntax_Syntax.as_arg uu____158 in
                                  [uu____157] in
                                uu____152 :: uu____154 in
                              uu____148 :: uu____149 in
                            uu____144 :: uu____145 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____142 uu____143 in
                        uu____141 FStar_Pervasives_Native.None rng in
                      FStar_Syntax_Syntax.as_arg uu____140 in
                    [uu____139] in
                  uu____135 :: uu____136 in
                FStar_Syntax_Syntax.mk_Tm_app uu____133 uu____134 in
              uu____132 FStar_Pervasives_Native.None rng
          | FStar_Tactics_Result.Success (a,ps) ->
              let uu____165 =
                let uu____166 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____167 =
                  let uu____168 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____169 =
                    let uu____172 =
                      let uu____173 =
                        let uu____174 =
                          let uu____175 =
                            FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                              [FStar_Syntax_Syntax.U_zero;
                              FStar_Syntax_Syntax.U_zero] in
                          let uu____176 =
                            let uu____177 = FStar_Syntax_Syntax.iarg t_a in
                            let uu____178 =
                              let uu____181 =
                                FStar_Syntax_Syntax.iarg t_proofstate in
                              let uu____182 =
                                let uu____185 =
                                  let uu____186 = embed_a rng a in
                                  FStar_Syntax_Syntax.as_arg uu____186 in
                                let uu____190 =
                                  let uu____193 =
                                    let uu____194 = embed_proofstate rng ps in
                                    FStar_Syntax_Syntax.as_arg uu____194 in
                                  [uu____193] in
                                uu____185 :: uu____190 in
                              uu____181 :: uu____182 in
                            uu____177 :: uu____178 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____175 uu____176 in
                        uu____174 FStar_Pervasives_Native.None rng in
                      FStar_Syntax_Syntax.as_arg uu____173 in
                    [uu____172] in
                  uu____168 :: uu____169 in
                FStar_Syntax_Syntax.mk_Tm_app uu____166 uu____167 in
              uu____165 FStar_Pervasives_Native.None rng
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
        let uu____253 = FStar_Syntax_Util.head_and_args tm1 in
        match uu____253 with
        | (hd1,args) ->
            let uu____302 =
              let uu____303 = FStar_Syntax_Util.un_uinst hd1 in
              uu____303.FStar_Syntax_Syntax.n in
            (uu____302, args) in
      let uu____314 = hd'_and_args t in
      match uu____314 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____344)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____381 =
            let uu____388 =
              FStar_Syntax_Embeddings.unembed_pair unembed_a
                unembed_proofstate in
            uu____388 tuple2 in
          FStar_Util.bind_opt uu____381
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inl x))
      | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____446)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____483 =
            let uu____490 =
              FStar_Syntax_Embeddings.unembed_pair
                FStar_Syntax_Embeddings.unembed_string unembed_proofstate in
            uu____490 tuple2 in
          FStar_Util.bind_opt uu____483
            (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inr x))
      | uu____541 ->
          ((let uu____555 =
              let uu____556 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded tactic result: %s"
                uu____556 in
            FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____555);
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
    let uu____585 =
      let uu____586 = FStar_Syntax_Subst.compress t in
      uu____586.FStar_Syntax_Syntax.n in
    match uu____585 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____593 ->
        ((let uu____595 =
            let uu____596 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded direction: %s" uu____596 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____595);
         FStar_Pervasives_Native.None)