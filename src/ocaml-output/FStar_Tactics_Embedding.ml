open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____15 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____15 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____21 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____21
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____32 = lid_as_data_fv l  in FStar_Syntax_Syntax.fv_to_tm uu____32
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____38 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____38
  
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
  let uu____39 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____39 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____40 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____40 
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____41 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.tconst uu____41 
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____42 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.fvconst uu____42 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____43 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____43 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____51 = let uu____62 = FStar_Syntax_Syntax.as_arg t  in [uu____62]
       in
    FStar_Syntax_Util.mk_app t_result uu____51
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____87 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____87 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____88 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____88 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____89 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____89 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____90 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____90 
let mk_emb :
  'a .
    (FStar_Range.range -> 'a -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
        -> FStar_Syntax_Syntax.term -> 'a FStar_Syntax_Embeddings.embedding
  =
  fun em  ->
    fun un  ->
      fun t  ->
        let uu____141 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____141
  
let embed :
  'Auu____187 .
    'Auu____187 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____187 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____207 = FStar_Syntax_Embeddings.embed e x  in
        uu____207 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____247 .
    Prims.bool ->
      'Auu____247 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____247 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____269 = FStar_Syntax_Embeddings.unembed e x  in
        uu____269 w FStar_Syntax_Embeddings.id_norm_cb
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',(FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                               FStar_Pervasives_Native.option)
                                 FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____300 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____300 with
    | (hd1,args) ->
        let uu____357 =
          let uu____358 = FStar_Syntax_Util.un_uinst hd1  in
          uu____358.FStar_Syntax_Syntax.n  in
        (uu____357, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____399 =
      let uu____400 = FStar_Syntax_Subst.compress t  in
      uu____400.FStar_Syntax_Syntax.n  in
    match uu____399 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____406;
          FStar_Syntax_Syntax.rng = uu____407;_}
        ->
        let uu____410 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
          uu____410
    | uu____413 ->
        (if w
         then
           (let uu____415 =
              let uu____420 =
                let uu____421 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____421
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____420)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____415)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_proofstate unembed_proofstate t_proofstate 
let (unfold_lazy_proofstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((proofstate)))" 
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv  ->
    fun us  ->
      fun ts  ->
        FStar_TypeChecker_NBETerm.mkFV fv (FStar_List.rev us)
          (FStar_List.rev ts)
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv  ->
    fun us  ->
      fun ts  ->
        FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us)
          (FStar_List.rev ts)
  
let (fv_as_emb_typ : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.emb_typ) =
  fun fv  ->
    let uu____503 =
      let uu____510 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____510, [])  in
    FStar_Syntax_Syntax.ET_app uu____503
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____527 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____527;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk =
      FStar_Common.mk_thunk
        (fun uu____532  ->
           FStar_TypeChecker_NBETerm.Constant
             (FStar_TypeChecker_NBETerm.String
                ("(((proofstate.nbe)))", FStar_Range.dummyRange)))
       in
    FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk)  in
  let unembed_proofstate _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
           FStar_Syntax_Syntax.ltyp = uu____603;
           FStar_Syntax_Syntax.rng = uu____604;_},uu____605)
        ->
        let uu____624 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
          uu____624
    | uu____627 ->
        ((let uu____629 =
            let uu____634 =
              let uu____635 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____635
               in
            (FStar_Errors.Warning_NotEmbedded, uu____634)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____629);
         FStar_Pervasives_Native.None)
     in
  let uu____636 = mkFV fv_proofstate [] []  in
  let uu____641 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____636;
    FStar_TypeChecker_NBETerm.emb_typ = uu____641
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____670 =
      let uu____671 = FStar_Syntax_Subst.compress t  in
      uu____671.FStar_Syntax_Syntax.n  in
    match uu____670 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____677;
          FStar_Syntax_Syntax.rng = uu____678;_}
        ->
        let uu____681 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _0_3  -> FStar_Pervasives_Native.Some _0_3)
          uu____681
    | uu____684 ->
        (if w
         then
           (let uu____686 =
              let uu____691 =
                let uu____692 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____692  in
              (FStar_Errors.Warning_NotEmbedded, uu____691)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____686)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_goal unembed_goal t_goal 
let (unfold_lazy_goal :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((goal)))" 
let (e_goal_nbe :
  FStar_Tactics_Types.goal FStar_TypeChecker_NBETerm.embedding) =
  let embed_goal _cb ps =
    let li =
      let uu____713 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____713;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk =
      FStar_Common.mk_thunk
        (fun uu____718  ->
           FStar_TypeChecker_NBETerm.Constant
             (FStar_TypeChecker_NBETerm.String
                ("(((goal.nbe)))", FStar_Range.dummyRange)))
       in
    FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk)  in
  let unembed_goal _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
           FStar_Syntax_Syntax.ltyp = uu____789;
           FStar_Syntax_Syntax.rng = uu____790;_},uu____791)
        ->
        let uu____810 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _0_4  -> FStar_Pervasives_Native.Some _0_4)
          uu____810
    | uu____813 ->
        ((let uu____815 =
            let uu____820 =
              let uu____821 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE goal: %s" uu____821  in
            (FStar_Errors.Warning_NotEmbedded, uu____820)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____815);
         FStar_Pervasives_Native.None)
     in
  let uu____822 = mkFV fv_goal [] []  in
  let uu____827 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____822;
    FStar_TypeChecker_NBETerm.emb_typ = uu____827
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____872 uu____873 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____896 =
          let uu____901 =
            let uu____902 =
              let uu____911 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____911  in
            [uu____902]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____901
           in
        uu____896 FStar_Pervasives_Native.None rng
    | FStar_Tactics_Types.EExn t ->
        let uu___355_931 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___355_931.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___355_931.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____934 = FStar_Util.message_of_exn e1  in
          Prims.strcat "uncaught exception: " uu____934  in
        let uu____935 =
          let uu____940 =
            let uu____941 =
              let uu____950 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____950  in
            [uu____941]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____940
           in
        uu____935 FStar_Pervasives_Native.None rng
     in
  let unembed_exn t w uu____988 =
    let uu____993 = hd'_and_args t  in
    match uu____993 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1012)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____1047 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____1047
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1052 -> FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____1067 =
    let uu____1068 =
      let uu____1075 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____1075, [])  in
    FStar_Syntax_Syntax.ET_app uu____1068  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____1079  -> "(exn)") uu____1067
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1094 =
          let uu____1101 =
            let uu____1106 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____1106  in
          [uu____1101]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____1094
    | uu____1115 ->
        let uu____1116 =
          let uu____1117 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____1117  in
        failwith uu____1116
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1134,(s,uu____1136)::[])
        when FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid
        ->
        let uu____1155 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1155
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1160 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____1162 = mkFV fv_exn [] []  in
  let uu____1167 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____1162;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1167
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____1228 uu____1229 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1255 =
            let uu____1260 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____1261 =
              let uu____1262 =
                let uu____1271 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____1271  in
              let uu____1272 =
                let uu____1283 =
                  let uu____1292 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1292  in
                let uu____1293 =
                  let uu____1304 =
                    let uu____1313 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____1313  in
                  [uu____1304]  in
                uu____1283 :: uu____1293  in
              uu____1262 :: uu____1272  in
            FStar_Syntax_Syntax.mk_Tm_app uu____1260 uu____1261  in
          uu____1255 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1350 =
            let uu____1355 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____1356 =
              let uu____1357 =
                let uu____1366 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____1366  in
              let uu____1367 =
                let uu____1378 =
                  let uu____1387 = embed e_exn rng e  in
                  FStar_Syntax_Syntax.as_arg uu____1387  in
                let uu____1388 =
                  let uu____1399 =
                    let uu____1408 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____1408  in
                  [uu____1399]  in
                uu____1378 :: uu____1388  in
              uu____1357 :: uu____1367  in
            FStar_Syntax_Syntax.mk_Tm_app uu____1355 uu____1356  in
          uu____1350 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____1464 =
      let uu____1471 = hd'_and_args t  in
      match uu____1471 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____1493)::(ps,uu____1495)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1562 = unembed' w ea a  in
          FStar_Util.bind_opt uu____1562
            (fun a1  ->
               let uu____1570 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1570
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____1582)::(ps,uu____1584)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1651 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____1651
            (fun e1  ->
               let uu____1659 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1659
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1668 ->
          (if w
           then
             (let uu____1684 =
                let uu____1689 =
                  let uu____1690 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1690
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____1689)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1684)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____1694 =
      let uu____1695 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____1695  in
    let uu____1696 =
      let uu____1697 =
        let uu____1704 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____1705 =
          let uu____1708 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____1708]  in
        (uu____1704, uu____1705)  in
      FStar_Syntax_Syntax.ET_app uu____1697  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1694 (fun uu____1714  -> "") uu____1696
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1752 =
            let uu____1759 =
              let uu____1764 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1764  in
            let uu____1765 =
              let uu____1772 =
                let uu____1777 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____1777  in
              let uu____1778 =
                let uu____1785 =
                  let uu____1790 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1790  in
                [uu____1785]  in
              uu____1772 :: uu____1778  in
            uu____1759 :: uu____1765  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____1752
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1809 =
            let uu____1816 =
              let uu____1821 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1821  in
            let uu____1822 =
              let uu____1829 =
                let uu____1834 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1834  in
              let uu____1835 =
                let uu____1842 =
                  let uu____1847 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1847  in
                [uu____1842]  in
              uu____1829 :: uu____1835  in
            uu____1816 :: uu____1822  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____1809
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1884,(ps,uu____1886)::(a,uu____1888)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1920 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____1920
            (fun a1  ->
               let uu____1928 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____1928
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1938,(ps,uu____1940)::(e,uu____1942)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1974 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____1974
            (fun e1  ->
               let uu____1982 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____1982
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1991 -> FStar_Pervasives_Native.None  in
    let uu____1994 = mkFV fv_result [] []  in
    let uu____1999 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____1994;
      FStar_TypeChecker_NBETerm.emb_typ = uu____1999
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____2030 =
      let uu____2031 = FStar_Syntax_Subst.compress t  in
      uu____2031.FStar_Syntax_Syntax.n  in
    match uu____2030 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2038 ->
        (if w
         then
           (let uu____2040 =
              let uu____2045 =
                let uu____2046 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2046
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2045)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2040)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_direction unembed_direction t_direction 
let (e_direction_nbe :
  FStar_Tactics_Types.direction FStar_TypeChecker_NBETerm.embedding) =
  let embed_direction cb res =
    match res with
    | FStar_Tactics_Types.TopDown  ->
        mkConstruct fstar_tactics_topdown_fv [] []
    | FStar_Tactics_Types.BottomUp  ->
        mkConstruct fstar_tactics_bottomup_fv [] []
     in
  let unembed_direction cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2085,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2101,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2116 ->
        ((let uu____2118 =
            let uu____2123 =
              let uu____2124 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____2124
               in
            (FStar_Errors.Warning_NotEmbedded, uu____2123)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2118);
         FStar_Pervasives_Native.None)
     in
  let uu____2125 = mkFV fv_direction [] []  in
  let uu____2130 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____2125;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2130
  } 
let (e_guard_policy :
  FStar_Tactics_Types.guard_policy FStar_Syntax_Embeddings.embedding) =
  let embed_guard_policy rng p =
    match p with
    | FStar_Tactics_Types.SMT  -> fstar_tactics_SMT
    | FStar_Tactics_Types.Goal  -> fstar_tactics_Goal
    | FStar_Tactics_Types.Force  -> fstar_tactics_Force
    | FStar_Tactics_Types.Drop  -> fstar_tactics_Drop  in
  let unembed_guard_policy w t =
    let uu____2159 =
      let uu____2160 = FStar_Syntax_Subst.compress t  in
      uu____2160.FStar_Syntax_Syntax.n  in
    match uu____2159 with
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
    | uu____2169 ->
        (if w
         then
           (let uu____2171 =
              let uu____2176 =
                let uu____2177 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____2177
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2176)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2171)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_guard_policy unembed_guard_policy t_guard_policy 
let (e_guard_policy_nbe :
  FStar_Tactics_Types.guard_policy FStar_TypeChecker_NBETerm.embedding) =
  let embed_guard_policy cb p =
    match p with
    | FStar_Tactics_Types.SMT  -> mkConstruct fstar_tactics_SMT_fv [] []
    | FStar_Tactics_Types.Goal  -> mkConstruct fstar_tactics_Goal_fv [] []
    | FStar_Tactics_Types.Force  -> mkConstruct fstar_tactics_Force_fv [] []
    | FStar_Tactics_Types.Drop  -> mkConstruct fstar_tactics_Drop_fv [] []
     in
  let unembed_guard_policy cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2226,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2242,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2258,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2274,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2289 -> FStar_Pervasives_Native.None  in
  let uu____2290 = mkFV fv_guard_policy [] []  in
  let uu____2295 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____2290;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2295
  } 