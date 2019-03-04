open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____68588 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____68588 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____68597 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_tm uu____68597
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____68614 = lid_as_data_fv l  in
    FStar_Syntax_Syntax.fv_to_tm uu____68614
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____68623 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____68623
  
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
  let uu____68709 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____68709 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____68716 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____68716 
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____68723 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.tconst uu____68723 
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____68730 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.fvconst uu____68730 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____68744 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____68744 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____68758 =
      let uu____68769 = FStar_Syntax_Syntax.as_arg t  in [uu____68769]  in
    FStar_Syntax_Util.mk_app t_result uu____68758
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____68795 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____68795 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____68802 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____68802 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____68809 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____68809 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____68816 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____68816 
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
        let uu____68875 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____68875
  
let embed :
  'Auu____68923 .
    'Auu____68923 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____68923 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____68943 = FStar_Syntax_Embeddings.embed e x  in
        uu____68943 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____68984 .
    Prims.bool ->
      'Auu____68984 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____68984 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____69008 = FStar_Syntax_Embeddings.unembed e x  in
        uu____69008 w FStar_Syntax_Embeddings.id_norm_cb
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____69040 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____69040 with
    | (hd1,args) ->
        let uu____69097 =
          let uu____69098 = FStar_Syntax_Util.un_uinst hd1  in
          uu____69098.FStar_Syntax_Syntax.n  in
        (uu____69097, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____69142 =
      let uu____69143 = FStar_Syntax_Subst.compress t  in
      uu____69143.FStar_Syntax_Syntax.n  in
    match uu____69142 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____69149;
          FStar_Syntax_Syntax.rng = uu____69150;_}
        ->
        let uu____69153 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _69156  -> FStar_Pervasives_Native.Some _69156) uu____69153
    | uu____69157 ->
        (if w
         then
           (let uu____69160 =
              let uu____69166 =
                let uu____69168 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s"
                  uu____69168
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____69166)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69160)
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
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
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
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv  ->
    fun us  ->
      fun ts  ->
        FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us)
          (FStar_List.rev ts)
  
let (fv_as_emb_typ : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.emb_typ) =
  fun fv  ->
    let uu____69259 =
      let uu____69267 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____69267, [])  in
    FStar_Syntax_Syntax.ET_app uu____69259
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____69287 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____69287;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____69292  ->
           FStar_TypeChecker_NBETerm.Constant
             (FStar_TypeChecker_NBETerm.String
                ("(((proofstate.nbe)))", FStar_Range.dummyRange)))
       in
    FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk1)  in
  let unembed_proofstate _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
           FStar_Syntax_Syntax.ltyp = uu____69365;
           FStar_Syntax_Syntax.rng = uu____69366;_},uu____69367)
        ->
        let uu____69386 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _69389  -> FStar_Pervasives_Native.Some _69389) uu____69386
    | uu____69390 ->
        ((let uu____69392 =
            let uu____69398 =
              let uu____69400 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____69400
               in
            (FStar_Errors.Warning_NotEmbedded, uu____69398)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____69392);
         FStar_Pervasives_Native.None)
     in
  let uu____69404 = mkFV fv_proofstate [] []  in
  let uu____69409 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____69404;
    FStar_TypeChecker_NBETerm.emb_typ = uu____69409
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____69441 =
      let uu____69442 = FStar_Syntax_Subst.compress t  in
      uu____69442.FStar_Syntax_Syntax.n  in
    match uu____69441 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____69448;
          FStar_Syntax_Syntax.rng = uu____69449;_}
        ->
        let uu____69452 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _69455  -> FStar_Pervasives_Native.Some _69455) uu____69452
    | uu____69456 ->
        (if w
         then
           (let uu____69459 =
              let uu____69465 =
                let uu____69467 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____69467  in
              (FStar_Errors.Warning_NotEmbedded, uu____69465)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69459)
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
      let uu____69495 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____69495;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____69500  ->
           FStar_TypeChecker_NBETerm.Constant
             (FStar_TypeChecker_NBETerm.String
                ("(((goal.nbe)))", FStar_Range.dummyRange)))
       in
    FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk1)  in
  let unembed_goal _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
           FStar_Syntax_Syntax.ltyp = uu____69573;
           FStar_Syntax_Syntax.rng = uu____69574;_},uu____69575)
        ->
        let uu____69594 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _69597  -> FStar_Pervasives_Native.Some _69597) uu____69594
    | uu____69598 ->
        ((let uu____69600 =
            let uu____69606 =
              let uu____69608 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE goal: %s" uu____69608
               in
            (FStar_Errors.Warning_NotEmbedded, uu____69606)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____69600);
         FStar_Pervasives_Native.None)
     in
  let uu____69612 = mkFV fv_goal [] []  in
  let uu____69617 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____69612;
    FStar_TypeChecker_NBETerm.emb_typ = uu____69617
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____69663 uu____69664 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____69688 =
          let uu____69693 =
            let uu____69694 =
              let uu____69703 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____69703  in
            [uu____69694]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____69693
           in
        uu____69688 FStar_Pervasives_Native.None rng
    | FStar_Tactics_Types.EExn t ->
        let uu___726_69724 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___726_69724.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___726_69724.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____69728 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____69728  in
        let uu____69731 =
          let uu____69736 =
            let uu____69737 =
              let uu____69746 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____69746  in
            [uu____69737]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____69736
           in
        uu____69731 FStar_Pervasives_Native.None rng
     in
  let unembed_exn t w uu____69786 =
    let uu____69792 = hd'_and_args t  in
    match uu____69792 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____69811)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____69846 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____69846
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____69855 ->
        FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____69870 =
    let uu____69871 =
      let uu____69879 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____69879, [])  in
    FStar_Syntax_Syntax.ET_app uu____69871  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____69886  -> "(exn)") uu____69870
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____69904 =
          let uu____69911 =
            let uu____69916 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____69916  in
          [uu____69911]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____69904
    | uu____69926 ->
        let uu____69927 =
          let uu____69929 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____69929  in
        failwith uu____69927
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____69948,(s,uu____69950)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____69969 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____69969
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____69978 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____69980 = mkFV fv_exn [] []  in
  let uu____69985 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____69980;
    FStar_TypeChecker_NBETerm.emb_typ = uu____69985
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____70047 uu____70048 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____70074 =
            let uu____70079 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____70080 =
              let uu____70081 =
                let uu____70090 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____70090  in
              let uu____70091 =
                let uu____70102 =
                  let uu____70111 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____70111  in
                let uu____70112 =
                  let uu____70123 =
                    let uu____70132 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____70132  in
                  [uu____70123]  in
                uu____70102 :: uu____70112  in
              uu____70081 :: uu____70091  in
            FStar_Syntax_Syntax.mk_Tm_app uu____70079 uu____70080  in
          uu____70074 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____70169 =
            let uu____70174 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____70175 =
              let uu____70176 =
                let uu____70185 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____70185  in
              let uu____70186 =
                let uu____70197 =
                  let uu____70206 = embed e_exn rng e  in
                  FStar_Syntax_Syntax.as_arg uu____70206  in
                let uu____70207 =
                  let uu____70218 =
                    let uu____70227 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____70227  in
                  [uu____70218]  in
                uu____70197 :: uu____70207  in
              uu____70176 :: uu____70186  in
            FStar_Syntax_Syntax.mk_Tm_app uu____70174 uu____70175  in
          uu____70169 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____70284 =
      let uu____70292 = hd'_and_args t  in
      match uu____70292 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____70314)::(ps,uu____70316)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____70383 = unembed' w ea a  in
          FStar_Util.bind_opt uu____70383
            (fun a1  ->
               let uu____70391 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____70391
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____70403)::(ps,uu____70405)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____70472 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____70472
            (fun e1  ->
               let uu____70480 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____70480
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____70489 ->
          (if w
           then
             (let uu____70506 =
                let uu____70512 =
                  let uu____70514 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____70514
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____70512)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____70506)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____70522 =
      let uu____70523 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____70523  in
    let uu____70524 =
      let uu____70525 =
        let uu____70533 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____70536 =
          let uu____70539 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____70539]  in
        (uu____70533, uu____70536)  in
      FStar_Syntax_Syntax.ET_app uu____70525  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____70522 (fun uu____70546  -> "") uu____70524
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____70586 =
            let uu____70593 =
              let uu____70598 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____70598  in
            let uu____70599 =
              let uu____70606 =
                let uu____70611 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____70611  in
              let uu____70612 =
                let uu____70619 =
                  let uu____70624 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____70624  in
                [uu____70619]  in
              uu____70606 :: uu____70612  in
            uu____70593 :: uu____70599  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____70586
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____70643 =
            let uu____70650 =
              let uu____70655 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____70655  in
            let uu____70656 =
              let uu____70663 =
                let uu____70668 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____70668  in
              let uu____70669 =
                let uu____70676 =
                  let uu____70681 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____70681  in
                [uu____70676]  in
              uu____70663 :: uu____70669  in
            uu____70650 :: uu____70656  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____70643
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____70718,(ps,uu____70720)::(a,uu____70722)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____70754 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____70754
            (fun a1  ->
               let uu____70762 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____70762
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____70772,(ps,uu____70774)::(e,uu____70776)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____70808 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____70808
            (fun e1  ->
               let uu____70816 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____70816
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____70825 -> FStar_Pervasives_Native.None  in
    let uu____70828 = mkFV fv_result [] []  in
    let uu____70833 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____70828;
      FStar_TypeChecker_NBETerm.emb_typ = uu____70833
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____70867 =
      let uu____70868 = FStar_Syntax_Subst.compress t  in
      uu____70868.FStar_Syntax_Syntax.n  in
    match uu____70867 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____70875 ->
        (if w
         then
           (let uu____70878 =
              let uu____70884 =
                let uu____70886 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s"
                  uu____70886
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____70884)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____70878)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____70930,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____70946,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____70961 ->
        ((let uu____70963 =
            let uu____70969 =
              let uu____70971 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____70971
               in
            (FStar_Errors.Warning_NotEmbedded, uu____70969)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____70963);
         FStar_Pervasives_Native.None)
     in
  let uu____70975 = mkFV fv_direction [] []  in
  let uu____70980 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____70975;
    FStar_TypeChecker_NBETerm.emb_typ = uu____70980
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
    let uu____71012 =
      let uu____71013 = FStar_Syntax_Subst.compress t  in
      uu____71013.FStar_Syntax_Syntax.n  in
    match uu____71012 with
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
    | uu____71022 ->
        (if w
         then
           (let uu____71025 =
              let uu____71031 =
                let uu____71033 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____71033
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____71031)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____71025)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____71087,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____71103,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____71119,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____71135,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____71150 -> FStar_Pervasives_Native.None  in
  let uu____71151 = mkFV fv_guard_policy [] []  in
  let uu____71156 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____71151;
    FStar_TypeChecker_NBETerm.emb_typ = uu____71156
  } 