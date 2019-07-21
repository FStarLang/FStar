open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s -> FStar_Parser_Const.fstar_tactics_lid' s
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l ->
    let uu____17 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu____17 FStar_Syntax_Syntax.fv_to_tm
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    let uu____26 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____26
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l ->
    let uu____43 = lid_as_data_fv l in FStar_Syntax_Syntax.fv_to_tm uu____43
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    let uu____52 = fstar_tactics_lid' ["Effect"; s] in
    lid_as_data_tm uu____52
let (fstar_tactics_Failed_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Failed"]
let (fstar_tactics_Success_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Result"; "Success"]
let (fstar_tactics_Failed_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Failed_lid
let (fstar_tactics_Success_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Success_lid
let (fstar_tactics_Failed_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Failed_lid
let (fstar_tactics_Success_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Success_lid
let (fstar_tactics_topdown_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "TopDown"]
let (fstar_tactics_bottomup_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "BottomUp"]
let (fstar_tactics_topdown : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_topdown_lid
let (fstar_tactics_bottomup : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_bottomup_lid
let (fstar_tactics_topdown_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_topdown_lid
let (fstar_tactics_bottomup_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_bottomup_lid
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
let (fstar_tactics_SMT_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_SMT_lid
let (fstar_tactics_Goal_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Goal_lid
let (fstar_tactics_Drop_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Drop_lid
let (fstar_tactics_Force_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Force_lid
let (fstar_tactics_TacticFailure_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "TacticFailure"]
let (fstar_tactics_EExn_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "EExn"]
let (fstar_tactics_TacticFailure_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_TacticFailure_lid
let (fstar_tactics_EExn_tm : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_EExn_lid
let (fstar_tactics_TacticFailure_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_TacticFailure_lid
let (fstar_tactics_EExn_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_EExn_lid
let (t_proofstate : FStar_Syntax_Syntax.term) =
  let uu____138 = fstar_tactics_lid' ["Types"; "proofstate"] in
  FStar_Syntax_Syntax.tconst uu____138
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____145 = fstar_tactics_lid' ["Types"; "proofstate"] in
  FStar_Syntax_Syntax.fvconst uu____145
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____152 = fstar_tactics_lid' ["Types"; "goal"] in
  FStar_Syntax_Syntax.tconst uu____152
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____159 = fstar_tactics_lid' ["Types"; "goal"] in
  FStar_Syntax_Syntax.fvconst uu____159
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"]
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____173 = fstar_tactics_lid' ["Types"; "result"] in
  FStar_Syntax_Syntax.fvconst uu____173
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu____187 =
      let uu____198 = FStar_Syntax_Syntax.as_arg t in [uu____198] in
    FStar_Syntax_Util.mk_app t_result uu____187
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____224 = fstar_tactics_lid' ["Types"; "guard_policy"] in
  FStar_Syntax_Syntax.tconst uu____224
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____231 = fstar_tactics_lid' ["Types"; "guard_policy"] in
  FStar_Syntax_Syntax.fvconst uu____231
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____238 = fstar_tactics_lid' ["Types"; "direction"] in
  FStar_Syntax_Syntax.tconst uu____238
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____245 = fstar_tactics_lid' ["Types"; "direction"] in
  FStar_Syntax_Syntax.fvconst uu____245
let mk_emb :
  'a .
    (FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
        -> FStar_Syntax_Syntax.term -> 'a FStar_Syntax_Embeddings.embedding
  =
  fun em ->
    fun un ->
      fun t ->
        let uu____304 = FStar_Syntax_Embeddings.term_as_fv t in
        FStar_Syntax_Embeddings.mk_emb
          (fun x -> fun r -> fun _topt -> fun _norm -> em r x)
          (fun x -> fun w -> fun _norm -> un w x) uu____304
let embed :
  'Auu____331 .
    'Auu____331 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____331 -> FStar_Syntax_Syntax.term
  =
  fun e ->
    fun r ->
      fun x ->
        let uu____351 = FStar_Syntax_Embeddings.embed e x in
        uu____351 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
let unembed' :
  'Auu____369 .
    Prims.bool ->
      'Auu____369 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____369 FStar_Pervasives_Native.option
  =
  fun w ->
    fun e ->
      fun x ->
        let uu____393 = FStar_Syntax_Embeddings.unembed e x in
        uu____393 w FStar_Syntax_Embeddings.id_norm_cb
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm ->
    let tm1 = FStar_Syntax_Util.unascribe tm in
    let uu____421 = FStar_Syntax_Util.head_and_args tm1 in
    match uu____421 with
    | (hd1, args) ->
        let uu____478 =
          let uu____479 = FStar_Syntax_Util.un_uinst hd1 in
          uu____479.FStar_Syntax_Syntax.n in
        (uu____478, args)
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng) in
  let unembed_proofstate w t =
    let uu____523 =
      let uu____524 = FStar_Syntax_Subst.compress t in
      uu____524.FStar_Syntax_Syntax.n in
    match uu____523 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
          FStar_Syntax_Syntax.ltyp = uu____530;
          FStar_Syntax_Syntax.rng = uu____531;_}
        ->
        let uu____534 = FStar_Dyn.undyn b in
        FStar_All.pipe_left (fun _537 -> FStar_Pervasives_Native.Some _537)
          uu____534
    | uu____538 ->
        (if w
         then
           (let uu____541 =
              let uu____547 =
                let uu____549 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____549 in
              (FStar_Errors.Warning_NotEmbedded, uu____547) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____541)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_proofstate unembed_proofstate t_proofstate
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_string "(((proofstate)))"
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStar_TypeChecker_NBETerm.mkFV fv (FStar_List.rev us)
          (FStar_List.rev ts)
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us)
          (FStar_List.rev ts)
let (fv_as_emb_typ : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.emb_typ) =
  fun fv ->
    let uu____640 =
      let uu____648 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      (uu____648, []) in
    FStar_Syntax_Syntax.ET_app uu____640
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____668 = FStar_Dyn.mkdyn ps in
      {
        FStar_Syntax_Syntax.blob = uu____668;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      } in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____673 ->
           FStar_TypeChecker_NBETerm.Constant
             (FStar_TypeChecker_NBETerm.String
                ("(((proofstate.nbe)))", FStar_Range.dummyRange))) in
    FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk1) in
  let unembed_proofstate _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
           FStar_Syntax_Syntax.ltyp = uu____706;
           FStar_Syntax_Syntax.rng = uu____707;_},
         uu____708)
        ->
        let uu____727 = FStar_Dyn.undyn b in
        FStar_All.pipe_left (fun _730 -> FStar_Pervasives_Native.Some _730)
          uu____727
    | uu____731 ->
        ((let uu____733 =
            let uu____739 =
              let uu____741 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____741 in
            (FStar_Errors.Warning_NotEmbedded, uu____739) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____733);
         FStar_Pervasives_Native.None) in
  let uu____745 = mkFV fv_proofstate [] [] in
  let uu____750 = fv_as_emb_typ fv_proofstate in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____745;
    FStar_TypeChecker_NBETerm.emb_typ = uu____750
  }
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng) in
  let unembed_goal w t =
    let uu____782 =
      let uu____783 = FStar_Syntax_Subst.compress t in
      uu____783.FStar_Syntax_Syntax.n in
    match uu____782 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
          FStar_Syntax_Syntax.ltyp = uu____789;
          FStar_Syntax_Syntax.rng = uu____790;_}
        ->
        let uu____793 = FStar_Dyn.undyn b in
        FStar_All.pipe_left (fun _796 -> FStar_Pervasives_Native.Some _796)
          uu____793
    | uu____797 ->
        (if w
         then
           (let uu____800 =
              let uu____806 =
                let uu____808 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded goal: %s" uu____808 in
              (FStar_Errors.Warning_NotEmbedded, uu____806) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____800)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_goal unembed_goal t_goal
let (unfold_lazy_goal :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_string "(((goal)))"
let (e_goal_nbe :
  FStar_Tactics_Types.goal FStar_TypeChecker_NBETerm.embedding) =
  let embed_goal _cb ps =
    let li =
      let uu____836 = FStar_Dyn.mkdyn ps in
      {
        FStar_Syntax_Syntax.blob = uu____836;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      } in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____841 ->
           FStar_TypeChecker_NBETerm.Constant
             (FStar_TypeChecker_NBETerm.String
                ("(((goal.nbe)))", FStar_Range.dummyRange))) in
    FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk1) in
  let unembed_goal _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
           FStar_Syntax_Syntax.ltyp = uu____874;
           FStar_Syntax_Syntax.rng = uu____875;_},
         uu____876)
        ->
        let uu____895 = FStar_Dyn.undyn b in
        FStar_All.pipe_left (fun _898 -> FStar_Pervasives_Native.Some _898)
          uu____895
    | uu____899 ->
        ((let uu____901 =
            let uu____907 =
              let uu____909 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded NBE goal: %s" uu____909 in
            (FStar_Errors.Warning_NotEmbedded, uu____907) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____901);
         FStar_Pervasives_Native.None) in
  let uu____913 = mkFV fv_goal [] [] in
  let uu____918 = fv_as_emb_typ fv_goal in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____913;
    FStar_TypeChecker_NBETerm.emb_typ = uu____918
  }
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____944 uu____945 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____949 =
          let uu____954 =
            let uu____955 =
              let uu____964 = embed FStar_Syntax_Embeddings.e_string rng s in
              FStar_Syntax_Syntax.as_arg uu____964 in
            [uu____955] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____954 in
        uu____949 FStar_Pervasives_Native.None rng
    | FStar_Tactics_Types.EExn t ->
        let uu___117_983 = t in
        {
          FStar_Syntax_Syntax.n = (uu___117_983.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___117_983.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____987 = FStar_Util.message_of_exn e1 in
          Prims.op_Hat "uncaught exception: " uu____987 in
        let uu____990 =
          let uu____995 =
            let uu____996 =
              let uu____1005 = embed FStar_Syntax_Embeddings.e_string rng s in
              FStar_Syntax_Syntax.as_arg uu____1005 in
            [uu____996] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____995 in
        uu____990 FStar_Pervasives_Native.None rng in
  let unembed_exn t w uu____1042 =
    let uu____1047 = hd'_and_args t in
    match uu____1047 with
    | (FStar_Syntax_Syntax.Tm_fvar fv, (s, uu____1066)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____1101 = unembed' w FStar_Syntax_Embeddings.e_string s in
        FStar_Util.bind_opt uu____1101
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1110 -> FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t) in
  let uu____1125 =
    let uu____1126 =
      let uu____1134 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid in
      (uu____1134, []) in
    FStar_Syntax_Syntax.ET_app uu____1126 in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____1141 -> "(exn)") uu____1125
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1159 =
          let uu____1166 =
            let uu____1171 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s in
            FStar_TypeChecker_NBETerm.as_arg uu____1171 in
          [uu____1166] in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____1159
    | uu____1181 ->
        let uu____1182 =
          let uu____1184 = FStar_Util.message_of_exn e in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____1184 in
        failwith uu____1182 in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____1203, (s, uu____1205)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____1224 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s in
        FStar_Util.bind_opt uu____1224
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1233 -> FStar_Pervasives_Native.None in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid in
  let uu____1235 = mkFV fv_exn [] [] in
  let uu____1240 = fv_as_emb_typ fv_exn in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____1235;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1240
  }
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea ->
    let embed_result res rng uu____1282 uu____1283 =
      match res with
      | FStar_Tactics_Result.Success (a, ps) ->
          let uu____1289 =
            let uu____1294 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero] in
            let uu____1295 =
              let uu____1296 =
                let uu____1305 = FStar_Syntax_Embeddings.type_of ea in
                FStar_Syntax_Syntax.iarg uu____1305 in
              let uu____1306 =
                let uu____1317 =
                  let uu____1326 = embed ea rng a in
                  FStar_Syntax_Syntax.as_arg uu____1326 in
                let uu____1327 =
                  let uu____1338 =
                    let uu____1347 = embed e_proofstate rng ps in
                    FStar_Syntax_Syntax.as_arg uu____1347 in
                  [uu____1338] in
                uu____1317 :: uu____1327 in
              uu____1296 :: uu____1306 in
            FStar_Syntax_Syntax.mk_Tm_app uu____1294 uu____1295 in
          uu____1289 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e, ps) ->
          let uu____1382 =
            let uu____1387 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero] in
            let uu____1388 =
              let uu____1389 =
                let uu____1398 = FStar_Syntax_Embeddings.type_of ea in
                FStar_Syntax_Syntax.iarg uu____1398 in
              let uu____1399 =
                let uu____1410 =
                  let uu____1419 = embed e_exn rng e in
                  FStar_Syntax_Syntax.as_arg uu____1419 in
                let uu____1420 =
                  let uu____1431 =
                    let uu____1440 = embed e_proofstate rng ps in
                    FStar_Syntax_Syntax.as_arg uu____1440 in
                  [uu____1431] in
                uu____1410 :: uu____1420 in
              uu____1389 :: uu____1399 in
            FStar_Syntax_Syntax.mk_Tm_app uu____1387 uu____1388 in
          uu____1382 FStar_Pervasives_Native.None rng in
    let unembed_result t w uu____1494 =
      let uu____1501 = hd'_and_args t in
      match uu____1501 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         _t::(a, uu____1523)::(ps, uu____1525)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1592 = unembed' w ea a in
          FStar_Util.bind_opt uu____1592
            (fun a1 ->
               let uu____1600 = unembed' w e_proofstate ps in
               FStar_Util.bind_opt uu____1600
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         _t::(e, uu____1612)::(ps, uu____1614)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1681 = unembed' w e_exn e in
          FStar_Util.bind_opt uu____1681
            (fun e1 ->
               let uu____1689 = unembed' w e_proofstate ps in
               FStar_Util.bind_opt uu____1689
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1698 ->
          (if w
           then
             (let uu____1715 =
                let uu____1721 =
                  let uu____1723 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1723 in
                (FStar_Errors.Warning_NotEmbedded, uu____1721) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1715)
           else ();
           FStar_Pervasives_Native.None) in
    let uu____1731 =
      let uu____1732 = FStar_Syntax_Embeddings.type_of ea in
      t_result_of uu____1732 in
    let uu____1733 =
      let uu____1734 =
        let uu____1742 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid in
        let uu____1745 =
          let uu____1748 = FStar_Syntax_Embeddings.emb_typ_of ea in
          [uu____1748] in
        (uu____1742, uu____1745) in
      FStar_Syntax_Syntax.ET_app uu____1734 in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1731 (fun uu____1755 -> "") uu____1733
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e, ps) ->
          let uu____1795 =
            let uu____1802 =
              let uu____1807 = FStar_TypeChecker_NBETerm.type_of ea in
              FStar_TypeChecker_NBETerm.as_iarg uu____1807 in
            let uu____1808 =
              let uu____1815 =
                let uu____1820 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e in
                FStar_TypeChecker_NBETerm.as_arg uu____1820 in
              let uu____1821 =
                let uu____1828 =
                  let uu____1833 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps in
                  FStar_TypeChecker_NBETerm.as_arg uu____1833 in
                [uu____1828] in
              uu____1815 :: uu____1821 in
            uu____1802 :: uu____1808 in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____1795
      | FStar_Tactics_Result.Success (a, ps) ->
          let uu____1852 =
            let uu____1859 =
              let uu____1864 = FStar_TypeChecker_NBETerm.type_of ea in
              FStar_TypeChecker_NBETerm.as_iarg uu____1864 in
            let uu____1865 =
              let uu____1872 =
                let uu____1877 = FStar_TypeChecker_NBETerm.embed ea cb a in
                FStar_TypeChecker_NBETerm.as_arg uu____1877 in
              let uu____1878 =
                let uu____1885 =
                  let uu____1890 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps in
                  FStar_TypeChecker_NBETerm.as_arg uu____1890 in
                [uu____1885] in
              uu____1872 :: uu____1878 in
            uu____1859 :: uu____1865 in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____1852 in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____1927, (ps, uu____1929)::(a, uu____1931)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1963 = FStar_TypeChecker_NBETerm.unembed ea cb a in
          FStar_Util.bind_opt uu____1963
            (fun a1 ->
               let uu____1971 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps in
               FStar_Util.bind_opt uu____1971
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____1981, (ps, uu____1983)::(e, uu____1985)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____2017 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e in
          FStar_Util.bind_opt uu____2017
            (fun e1 ->
               let uu____2025 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps in
               FStar_Util.bind_opt uu____2025
                 (fun ps1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____2034 -> FStar_Pervasives_Native.None in
    let uu____2037 = mkFV fv_result [] [] in
    let uu____2042 = fv_as_emb_typ fv_result in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____2037;
      FStar_TypeChecker_NBETerm.emb_typ = uu____2042
    }
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp -> fstar_tactics_bottomup in
  let unembed_direction w t =
    let uu____2076 =
      let uu____2077 = FStar_Syntax_Subst.compress t in
      uu____2077.FStar_Syntax_Syntax.n in
    match uu____2076 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2084 ->
        (if w
         then
           (let uu____2087 =
              let uu____2093 =
                let uu____2095 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2095 in
              (FStar_Errors.Warning_NotEmbedded, uu____2093) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2087)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_direction unembed_direction t_direction
let (e_direction_nbe :
  FStar_Tactics_Types.direction FStar_TypeChecker_NBETerm.embedding) =
  let embed_direction cb res =
    match res with
    | FStar_Tactics_Types.TopDown ->
        mkConstruct fstar_tactics_topdown_fv [] []
    | FStar_Tactics_Types.BottomUp ->
        mkConstruct fstar_tactics_bottomup_fv [] [] in
  let unembed_direction cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2139, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2155, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2170 ->
        ((let uu____2172 =
            let uu____2178 =
              let uu____2180 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded direction: %s" uu____2180 in
            (FStar_Errors.Warning_NotEmbedded, uu____2178) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2172);
         FStar_Pervasives_Native.None) in
  let uu____2184 = mkFV fv_direction [] [] in
  let uu____2189 = fv_as_emb_typ fv_direction in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____2184;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2189
  }
let (e_guard_policy :
  FStar_Tactics_Types.guard_policy FStar_Syntax_Embeddings.embedding) =
  let embed_guard_policy rng p =
    match p with
    | FStar_Tactics_Types.SMT -> fstar_tactics_SMT
    | FStar_Tactics_Types.Goal -> fstar_tactics_Goal
    | FStar_Tactics_Types.Force -> fstar_tactics_Force
    | FStar_Tactics_Types.Drop -> fstar_tactics_Drop in
  let unembed_guard_policy w t =
    let uu____2221 =
      let uu____2222 = FStar_Syntax_Subst.compress t in
      uu____2222.FStar_Syntax_Syntax.n in
    match uu____2221 with
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
    | uu____2231 ->
        (if w
         then
           (let uu____2234 =
              let uu____2240 =
                let uu____2242 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____2242 in
              (FStar_Errors.Warning_NotEmbedded, uu____2240) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2234)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_guard_policy unembed_guard_policy t_guard_policy
let (e_guard_policy_nbe :
  FStar_Tactics_Types.guard_policy FStar_TypeChecker_NBETerm.embedding) =
  let embed_guard_policy cb p =
    match p with
    | FStar_Tactics_Types.SMT -> mkConstruct fstar_tactics_SMT_fv [] []
    | FStar_Tactics_Types.Goal -> mkConstruct fstar_tactics_Goal_fv [] []
    | FStar_Tactics_Types.Force -> mkConstruct fstar_tactics_Force_fv [] []
    | FStar_Tactics_Types.Drop -> mkConstruct fstar_tactics_Drop_fv [] [] in
  let unembed_guard_policy cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2296, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2312, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2328, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____2344, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2359 -> FStar_Pervasives_Native.None in
  let uu____2360 = mkFV fv_guard_policy [] [] in
  let uu____2365 = fv_as_emb_typ fv_guard_policy in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____2360;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2365
  }