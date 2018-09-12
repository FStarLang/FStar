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
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____410
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
        FStar_All.pipe_left
          (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____624
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
        FStar_All.pipe_left
          (fun _0_18  -> FStar_Pervasives_Native.Some _0_18) uu____681
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
        FStar_All.pipe_left
          (fun _0_19  -> FStar_Pervasives_Native.Some _0_19) uu____810
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
        let uu___352_931 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___352_931.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___352_931.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s = FStar_Util.message_of_exn e1  in
        let uu____934 =
          let uu____939 =
            let uu____940 =
              let uu____949 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____949  in
            [uu____940]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____939
           in
        uu____934 FStar_Pervasives_Native.None rng
     in
  let unembed_exn t w uu____987 =
    let uu____992 = hd'_and_args t  in
    match uu____992 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1011)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____1046 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____1046
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1051 -> FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____1066 =
    let uu____1067 =
      let uu____1074 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____1074, [])  in
    FStar_Syntax_Syntax.ET_app uu____1067  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____1078  -> "(exn)") uu____1066
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1093 =
          let uu____1100 =
            let uu____1105 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____1105  in
          [uu____1100]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____1093
    | uu____1114 ->
        let uu____1115 =
          let uu____1116 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____1116  in
        failwith uu____1115
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1133,(s,uu____1135)::[])
        when FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid
        ->
        let uu____1154 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1154
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1159 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____1161 = mkFV fv_exn [] []  in
  let uu____1166 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____1161;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1166
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____1227 uu____1228 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1254 =
            let uu____1259 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____1260 =
              let uu____1261 =
                let uu____1270 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____1270  in
              let uu____1271 =
                let uu____1282 =
                  let uu____1291 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1291  in
                let uu____1292 =
                  let uu____1303 =
                    let uu____1312 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____1312  in
                  [uu____1303]  in
                uu____1282 :: uu____1292  in
              uu____1261 :: uu____1271  in
            FStar_Syntax_Syntax.mk_Tm_app uu____1259 uu____1260  in
          uu____1254 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1349 =
            let uu____1354 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____1355 =
              let uu____1356 =
                let uu____1365 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____1365  in
              let uu____1366 =
                let uu____1377 =
                  let uu____1386 = embed e_exn rng e  in
                  FStar_Syntax_Syntax.as_arg uu____1386  in
                let uu____1387 =
                  let uu____1398 =
                    let uu____1407 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____1407  in
                  [uu____1398]  in
                uu____1377 :: uu____1387  in
              uu____1356 :: uu____1366  in
            FStar_Syntax_Syntax.mk_Tm_app uu____1354 uu____1355  in
          uu____1349 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____1463 =
      let uu____1470 = hd'_and_args t  in
      match uu____1470 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____1492)::(ps,uu____1494)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1561 = unembed' w ea a  in
          FStar_Util.bind_opt uu____1561
            (fun a1  ->
               let uu____1569 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1569
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____1581)::(ps,uu____1583)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1650 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____1650
            (fun e1  ->
               let uu____1658 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1658
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1667 ->
          (if w
           then
             (let uu____1683 =
                let uu____1688 =
                  let uu____1689 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1689
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____1688)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1683)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____1693 =
      let uu____1694 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____1694  in
    let uu____1695 =
      let uu____1696 =
        let uu____1703 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____1704 =
          let uu____1707 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____1707]  in
        (uu____1703, uu____1704)  in
      FStar_Syntax_Syntax.ET_app uu____1696  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1693 (fun uu____1713  -> "") uu____1695
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1751 =
            let uu____1758 =
              let uu____1763 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1763  in
            let uu____1764 =
              let uu____1771 =
                let uu____1776 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____1776  in
              let uu____1777 =
                let uu____1784 =
                  let uu____1789 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1789  in
                [uu____1784]  in
              uu____1771 :: uu____1777  in
            uu____1758 :: uu____1764  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____1751
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1808 =
            let uu____1815 =
              let uu____1820 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1820  in
            let uu____1821 =
              let uu____1828 =
                let uu____1833 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1833  in
              let uu____1834 =
                let uu____1841 =
                  let uu____1846 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1846  in
                [uu____1841]  in
              uu____1828 :: uu____1834  in
            uu____1815 :: uu____1821  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____1808
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1883,(ps,uu____1885)::(a,uu____1887)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1919 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____1919
            (fun a1  ->
               let uu____1927 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____1927
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1937,(ps,uu____1939)::(e,uu____1941)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1973 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____1973
            (fun e1  ->
               let uu____1981 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____1981
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1990 -> FStar_Pervasives_Native.None  in
    let uu____1993 = mkFV fv_result [] []  in
    let uu____1998 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____1993;
      FStar_TypeChecker_NBETerm.emb_typ = uu____1998
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____2029 =
      let uu____2030 = FStar_Syntax_Subst.compress t  in
      uu____2030.FStar_Syntax_Syntax.n  in
    match uu____2029 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2037 ->
        (if w
         then
           (let uu____2039 =
              let uu____2044 =
                let uu____2045 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2045
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2044)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2039)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2084,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2100,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2115 ->
        ((let uu____2117 =
            let uu____2122 =
              let uu____2123 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____2123
               in
            (FStar_Errors.Warning_NotEmbedded, uu____2122)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2117);
         FStar_Pervasives_Native.None)
     in
  let uu____2124 = mkFV fv_direction [] []  in
  let uu____2129 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____2124;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2129
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
    let uu____2158 =
      let uu____2159 = FStar_Syntax_Subst.compress t  in
      uu____2159.FStar_Syntax_Syntax.n  in
    match uu____2158 with
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
    | uu____2168 ->
        (if w
         then
           (let uu____2170 =
              let uu____2175 =
                let uu____2176 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____2176
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2175)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2170)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2225,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2241,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2257,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2273,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2288 -> FStar_Pervasives_Native.None  in
  let uu____2289 = mkFV fv_guard_policy [] []  in
  let uu____2294 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____2289;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2294
  } 