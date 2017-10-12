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
  FStar_Tactics_Types.proofstate -> FStar_Syntax_Syntax.term =
  fun ps  ->
    FStar_Syntax_Util.mk_alien t_proofstate ps "tactics.embed_proofstate"
      FStar_Pervasives_Native.None
let unembed_proofstate:
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.proofstate FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____70 =
        let uu____71 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____71 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____70
    with
    | uu____78 ->
        ((let uu____80 =
            let uu____81 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded proofstate: %s" uu____81 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____80);
         FStar_Pervasives_Native.None)
let mk_app:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun hd1  ->
    fun args  ->
      FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
        FStar_Range.dummyRange
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
              let uu____130 =
                FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____131 =
                let uu____132 = FStar_Syntax_Syntax.iarg t_a in
                let uu____133 =
                  let uu____136 =
                    let uu____137 =
                      let uu____138 =
                        FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                          [FStar_Syntax_Syntax.U_zero;
                          FStar_Syntax_Syntax.U_zero] in
                      let uu____139 =
                        let uu____140 =
                          FStar_Syntax_Syntax.iarg
                            FStar_Syntax_Syntax.t_string in
                        let uu____141 =
                          let uu____144 =
                            FStar_Syntax_Syntax.iarg t_proofstate in
                          let uu____145 =
                            let uu____148 =
                              let uu____149 =
                                FStar_Syntax_Embeddings.embed_string msg in
                              FStar_Syntax_Syntax.as_arg uu____149 in
                            let uu____150 =
                              let uu____153 =
                                let uu____154 = embed_proofstate ps1 in
                                FStar_Syntax_Syntax.as_arg uu____154 in
                              [uu____153] in
                            uu____148 :: uu____150 in
                          uu____144 :: uu____145 in
                        uu____140 :: uu____141 in
                      mk_app uu____138 uu____139 in
                    FStar_Syntax_Syntax.as_arg uu____137 in
                  [uu____136] in
                uu____132 :: uu____133 in
              mk_app uu____130 uu____131
          | FStar_Tactics_Result.Success (a,ps1) ->
              let uu____157 =
                FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                  [FStar_Syntax_Syntax.U_zero] in
              let uu____158 =
                let uu____159 = FStar_Syntax_Syntax.iarg t_a in
                let uu____160 =
                  let uu____163 =
                    let uu____164 =
                      let uu____165 =
                        FStar_Syntax_Syntax.mk_Tm_uinst mktuple2_tm
                          [FStar_Syntax_Syntax.U_zero;
                          FStar_Syntax_Syntax.U_zero] in
                      let uu____166 =
                        let uu____167 = FStar_Syntax_Syntax.iarg t_a in
                        let uu____168 =
                          let uu____171 =
                            FStar_Syntax_Syntax.iarg t_proofstate in
                          let uu____172 =
                            let uu____175 =
                              let uu____176 = embed_a a in
                              FStar_Syntax_Syntax.as_arg uu____176 in
                            let uu____177 =
                              let uu____180 =
                                let uu____181 = embed_proofstate ps1 in
                                FStar_Syntax_Syntax.as_arg uu____181 in
                              [uu____180] in
                            uu____175 :: uu____177 in
                          uu____171 :: uu____172 in
                        uu____167 :: uu____168 in
                      mk_app uu____165 uu____166 in
                    FStar_Syntax_Syntax.as_arg uu____164 in
                  [uu____163] in
                uu____159 :: uu____160 in
              mk_app uu____157 uu____158
let unembed_result:
  'a .
    FStar_Tactics_Types.proofstate ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
          (('a,FStar_Tactics_Types.proofstate) FStar_Pervasives_Native.tuple2,
            (Prims.string,FStar_Tactics_Types.proofstate)
              FStar_Pervasives_Native.tuple2)
            FStar_Util.either FStar_Pervasives_Native.option
  =
  fun ps  ->
    fun t  ->
      fun unembed_a  ->
        let hd'_and_args tm =
          let tm1 = FStar_Syntax_Util.unascribe tm in
          let uu____243 = FStar_Syntax_Util.head_and_args tm1 in
          match uu____243 with
          | (hd1,args) ->
              let uu____292 =
                let uu____293 = FStar_Syntax_Util.un_uinst hd1 in
                uu____293.FStar_Syntax_Syntax.n in
              (uu____292, args) in
        let uu____304 = hd'_and_args t in
        match uu____304 with
        | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____334)::[]) when
            FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
            let uu____371 =
              FStar_Syntax_Embeddings.unembed_pair unembed_a
                unembed_proofstate tuple2 in
            FStar_Util.bind_opt uu____371
              (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inl x))
        | (FStar_Syntax_Syntax.Tm_fvar fv,_t::(tuple2,uu____423)::[]) when
            FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
            let uu____460 =
              FStar_Syntax_Embeddings.unembed_pair
                FStar_Syntax_Embeddings.unembed_string unembed_proofstate
                tuple2 in
            FStar_Util.bind_opt uu____460
              (fun x  -> FStar_Pervasives_Native.Some (FStar_Util.Inr x))
        | uu____509 ->
            ((let uu____523 =
                let uu____524 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded tactic result: %s"
                  uu____524 in
              FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____523);
             FStar_Pervasives_Native.None)
let embed_direction:
  FStar_Tactics_Types.direction -> FStar_Syntax_Syntax.term =
  fun d  ->
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup
let unembed_direction:
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.direction FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____549 =
      let uu____550 = FStar_Syntax_Subst.compress t in
      uu____550.FStar_Syntax_Syntax.n in
    match uu____549 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____557 ->
        ((let uu____559 =
            let uu____560 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Not an embedded direction: %s" uu____560 in
          FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____559);
         FStar_Pervasives_Native.None)