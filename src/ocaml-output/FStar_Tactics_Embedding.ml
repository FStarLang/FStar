open Prims
type name = FStar_Syntax_Syntax.bv[@@deriving show]
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s -> FStar_Parser_Const.fstar_tactics_lid' s
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l ->
    let uu____11 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu____11 FStar_Syntax_Syntax.fv_to_tm
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    let uu____15 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____15
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l ->
    let uu____19 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____19
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    let uu____23 = fstar_tactics_lid' ["Effect"; s] in
    lid_as_data_tm uu____23
let (fstar_tactics_Failed_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Failed"]
let (fstar_tactics_Success_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Success"]
let (fstar_tactics_Failed_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Failed_lid
let (fstar_tactics_Success_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Success_lid
let (fstar_tactics_topdown_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "TopDown"]
let (fstar_tactics_bottomup_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "BottomUp"]
let (fstar_tactics_topdown : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_topdown_lid
let (fstar_tactics_bottomup : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_bottomup_lid
let (fstar_tactics_SMT_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "SMT"]
let (fstar_tactics_Goal_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Goal"]
let (fstar_tactics_Drop_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Drop"]
let (fstar_tactics_Force_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Force"]
let (fstar_tactics_SMT : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_SMT_lid
let (fstar_tactics_Goal : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Goal_lid
let (fstar_tactics_Drop : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Drop_lid
let (fstar_tactics_Force : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Force_lid
let (mktuple2_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm FStar_Parser_Const.lid_Mktuple2
let (t_proofstate : FStar_Syntax_Syntax.term) =
  let uu____24 = fstar_tactics_lid' ["Types"; "proofstate"] in
  FStar_Syntax_Syntax.tconst uu____24
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____25 = fstar_tactics_lid' ["Types"; "guard_policy"] in
  FStar_Syntax_Syntax.tconst uu____25
let (pair_typ :
  FStar_Reflection_Data.typ ->
    FStar_Reflection_Data.typ -> FStar_Reflection_Data.typ)
  =
  fun t ->
    fun s ->
      let uu____32 =
        let uu____33 =
          let uu____34 = lid_as_tm FStar_Parser_Const.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____34
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____35 =
          let uu____36 = FStar_Syntax_Syntax.as_arg t in
          let uu____37 =
            let uu____40 = FStar_Syntax_Syntax.as_arg s in [uu____40] in
          uu____36 :: uu____37 in
        FStar_Syntax_Syntax.mk_Tm_app uu____33 uu____35 in
      uu____32 FStar_Pervasives_Native.None FStar_Range.dummyRange
let (embed_proofstate :
  FStar_Range.range ->
    FStar_Tactics_Types.proofstate -> FStar_Syntax_Syntax.term)
  =
  fun rng ->
    fun ps ->
      FStar_Syntax_Util.mk_lazy ps t_proofstate
        FStar_Syntax_Syntax.Lazy_proofstate
        (FStar_Pervasives_Native.Some rng)
let (unembed_proofstate :
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.proofstate FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____61 =
      let uu____62 = FStar_Syntax_Subst.compress t in
      uu____62.FStar_Syntax_Syntax.n in
    match uu____61 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_proofstate ->
        let uu____68 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob in
        FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some _0_40)
          uu____68
    | uu____71 ->
        ((let uu____73 =
            let uu____78 =
              let uu____79 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded proofstate: %s" uu____79 in
            (FStar_Errors.Warning_NotEmbedded, uu____78) in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____73);
         FStar_Pervasives_Native.None)
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_string "(((proofstate)))"
let embed_result :
  'a .
    'a FStar_Syntax_Embeddings.embedder ->
      FStar_Reflection_Data.typ ->
        'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedder
  =
  fun embed_a ->
    fun t_a ->
      fun rng ->
        fun res ->
          match res with
          | FStar_Tactics_Result.Failed (msg, ps) ->
              let uu____126 =
                let uu____127 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____128 =
                  let uu____129 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____130 =
                    let uu____133 =
                      let uu____134 =
                        FStar_Syntax_Embeddings.embed_string rng msg in
                      FStar_Syntax_Syntax.as_arg uu____134 in
                    let uu____135 =
                      let uu____138 =
                        let uu____139 = embed_proofstate rng ps in
                        FStar_Syntax_Syntax.as_arg uu____139 in
                      [uu____138] in
                    uu____133 :: uu____135 in
                  uu____129 :: uu____130 in
                FStar_Syntax_Syntax.mk_Tm_app uu____127 uu____128 in
              uu____126 FStar_Pervasives_Native.None rng
          | FStar_Tactics_Result.Success (a, ps) ->
              let uu____144 =
                let uu____145 =
                  FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                    [FStar_Syntax_Syntax.U_zero] in
                let uu____146 =
                  let uu____147 = FStar_Syntax_Syntax.iarg t_a in
                  let uu____148 =
                    let uu____151 =
                      let uu____152 = embed_a rng a in
                      FStar_Syntax_Syntax.as_arg uu____152 in
                    let uu____156 =
                      let uu____159 =
                        let uu____160 = embed_proofstate rng ps in
                        FStar_Syntax_Syntax.as_arg uu____160 in
                      [uu____159] in
                    uu____151 :: uu____156 in
                  uu____147 :: uu____148 in
                FStar_Syntax_Syntax.mk_Tm_app uu____145 uu____146 in
              uu____144 FStar_Pervasives_Native.None rng
let unembed_result :
  'a .
    FStar_Syntax_Syntax.term ->
      'a FStar_Syntax_Embeddings.unembedder ->
        (('a, FStar_Tactics_Types.proofstate) FStar_Pervasives_Native.tuple2,
          (Prims.string, FStar_Tactics_Types.proofstate)
            FStar_Pervasives_Native.tuple2)
          FStar_Util.either FStar_Pervasives_Native.option
  =
  fun t ->
    fun unembed_a ->
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm in
        let uu____214 = FStar_Syntax_Util.head_and_args tm1 in
        match uu____214 with
        | (hd1, args) ->
            let uu____263 =
              let uu____264 = FStar_Syntax_Util.un_uinst hd1 in
              uu____264.FStar_Syntax_Syntax.n in
            (uu____263, args) in
      let uu____275 = hd'_and_args t in
      match uu____275 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         _t::(a, uu____305)::(ps, uu____307)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____354 = unembed_a a in
          FStar_Util.bind_opt uu____354
            (fun a1 ->
               let uu____374 = unembed_proofstate ps in
               FStar_Util.bind_opt uu____374
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some (FStar_Util.Inl (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         _t::(msg, uu____414)::(ps, uu____416)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____463 = FStar_Syntax_Embeddings.unembed_string msg in
          FStar_Util.bind_opt uu____463
            (fun msg1 ->
               let uu____481 = unembed_proofstate ps in
               FStar_Util.bind_opt uu____481
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some (FStar_Util.Inr (msg1, ps1))))
      | uu____518 ->
          ((let uu____532 =
              let uu____537 =
                let uu____538 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded tactic result: %s"
                  uu____538 in
              (FStar_Errors.Warning_NotEmbedded, uu____537) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____532);
           FStar_Pervasives_Native.None)
let (embed_direction :
  FStar_Range.range ->
    FStar_Tactics_Types.direction -> FStar_Syntax_Syntax.term)
  =
  fun rng ->
    fun d ->
      match d with
      | FStar_Tactics_Types.TopDown -> fstar_tactics_topdown
      | FStar_Tactics_Types.BottomUp -> fstar_tactics_bottomup
let (unembed_direction :
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.direction FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____569 =
      let uu____570 = FStar_Syntax_Subst.compress t in
      uu____570.FStar_Syntax_Syntax.n in
    match uu____569 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____577 ->
        ((let uu____579 =
            let uu____584 =
              let uu____585 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded direction: %s" uu____585 in
            (FStar_Errors.Warning_NotEmbedded, uu____584) in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____579);
         FStar_Pervasives_Native.None)
let (embed_guard_policy :
  FStar_Range.range ->
    FStar_Tactics_Types.guard_policy -> FStar_Syntax_Syntax.term)
  =
  fun rng ->
    fun p ->
      match p with
      | FStar_Tactics_Types.SMT -> fstar_tactics_SMT
      | FStar_Tactics_Types.Goal -> fstar_tactics_Goal
      | FStar_Tactics_Types.Force -> fstar_tactics_Force
      | FStar_Tactics_Types.Drop -> fstar_tactics_Drop
let (unembed_guard_policy :
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Types.guard_policy FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____604 =
      let uu____605 = FStar_Syntax_Subst.compress t in
      uu____605.FStar_Syntax_Syntax.n in
    match uu____604 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____614 ->
        ((let uu____616 =
            let uu____621 =
              let uu____622 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded guard_policy: %s" uu____622 in
            (FStar_Errors.Warning_NotEmbedded, uu____621) in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____616);
         FStar_Pervasives_Native.None)