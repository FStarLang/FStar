open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____68491 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____68491 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____68500 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_tm uu____68500
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____68517 = lid_as_data_fv l  in
    FStar_Syntax_Syntax.fv_to_tm uu____68517
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____68526 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____68526
  
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
  let uu____68612 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____68612 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____68619 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____68619 
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____68626 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.tconst uu____68626 
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____68633 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.fvconst uu____68633 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____68647 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____68647 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____68661 =
      let uu____68672 = FStar_Syntax_Syntax.as_arg t  in [uu____68672]  in
    FStar_Syntax_Util.mk_app t_result uu____68661
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____68698 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____68698 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____68705 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____68705 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____68712 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____68712 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____68719 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____68719 
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
        let uu____68778 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____68778
  
let embed :
  'Auu____68826 .
    'Auu____68826 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____68826 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____68846 = FStar_Syntax_Embeddings.embed e x  in
        uu____68846 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____68887 .
    Prims.bool ->
      'Auu____68887 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____68887 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____68911 = FStar_Syntax_Embeddings.unembed e x  in
        uu____68911 w FStar_Syntax_Embeddings.id_norm_cb
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____68943 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____68943 with
    | (hd1,args) ->
        let uu____69000 =
          let uu____69001 = FStar_Syntax_Util.un_uinst hd1  in
          uu____69001.FStar_Syntax_Syntax.n  in
        (uu____69000, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____69045 =
      let uu____69046 = FStar_Syntax_Subst.compress t  in
      uu____69046.FStar_Syntax_Syntax.n  in
    match uu____69045 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____69052;
          FStar_Syntax_Syntax.rng = uu____69053;_}
        ->
        let uu____69056 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _69059  -> FStar_Pervasives_Native.Some _69059) uu____69056
    | uu____69060 ->
        (if w
         then
           (let uu____69063 =
              let uu____69069 =
                let uu____69071 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s"
                  uu____69071
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____69069)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69063)
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
    let uu____69162 =
      let uu____69170 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____69170, [])  in
    FStar_Syntax_Syntax.ET_app uu____69162
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____69190 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____69190;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____69195  ->
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
           FStar_Syntax_Syntax.ltyp = uu____69268;
           FStar_Syntax_Syntax.rng = uu____69269;_},uu____69270)
        ->
        let uu____69289 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _69292  -> FStar_Pervasives_Native.Some _69292) uu____69289
    | uu____69293 ->
        ((let uu____69295 =
            let uu____69301 =
              let uu____69303 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____69303
               in
            (FStar_Errors.Warning_NotEmbedded, uu____69301)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____69295);
         FStar_Pervasives_Native.None)
     in
  let uu____69307 = mkFV fv_proofstate [] []  in
  let uu____69312 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____69307;
    FStar_TypeChecker_NBETerm.emb_typ = uu____69312
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____69344 =
      let uu____69345 = FStar_Syntax_Subst.compress t  in
      uu____69345.FStar_Syntax_Syntax.n  in
    match uu____69344 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____69351;
          FStar_Syntax_Syntax.rng = uu____69352;_}
        ->
        let uu____69355 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _69358  -> FStar_Pervasives_Native.Some _69358) uu____69355
    | uu____69359 ->
        (if w
         then
           (let uu____69362 =
              let uu____69368 =
                let uu____69370 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____69370  in
              (FStar_Errors.Warning_NotEmbedded, uu____69368)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69362)
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
      let uu____69398 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____69398;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____69403  ->
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
           FStar_Syntax_Syntax.ltyp = uu____69476;
           FStar_Syntax_Syntax.rng = uu____69477;_},uu____69478)
        ->
        let uu____69497 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _69500  -> FStar_Pervasives_Native.Some _69500) uu____69497
    | uu____69501 ->
        ((let uu____69503 =
            let uu____69509 =
              let uu____69511 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE goal: %s" uu____69511
               in
            (FStar_Errors.Warning_NotEmbedded, uu____69509)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____69503);
         FStar_Pervasives_Native.None)
     in
  let uu____69515 = mkFV fv_goal [] []  in
  let uu____69520 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____69515;
    FStar_TypeChecker_NBETerm.emb_typ = uu____69520
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____69566 uu____69567 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____69591 =
          let uu____69596 =
            let uu____69597 =
              let uu____69606 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____69606  in
            [uu____69597]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____69596
           in
        uu____69591 FStar_Pervasives_Native.None rng
    | FStar_Tactics_Types.EExn t ->
        let uu___726_69627 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___726_69627.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___726_69627.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____69631 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____69631  in
        let uu____69634 =
          let uu____69639 =
            let uu____69640 =
              let uu____69649 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____69649  in
            [uu____69640]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____69639
           in
        uu____69634 FStar_Pervasives_Native.None rng
     in
  let unembed_exn t w uu____69689 =
    let uu____69695 = hd'_and_args t  in
    match uu____69695 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____69714)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____69749 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____69749
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____69758 ->
        FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____69773 =
    let uu____69774 =
      let uu____69782 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____69782, [])  in
    FStar_Syntax_Syntax.ET_app uu____69774  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____69789  -> "(exn)") uu____69773
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____69807 =
          let uu____69814 =
            let uu____69819 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____69819  in
          [uu____69814]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____69807
    | uu____69829 ->
        let uu____69830 =
          let uu____69832 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____69832  in
        failwith uu____69830
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____69851,(s,uu____69853)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____69872 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____69872
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____69881 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____69883 = mkFV fv_exn [] []  in
  let uu____69888 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____69883;
    FStar_TypeChecker_NBETerm.emb_typ = uu____69888
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____69950 uu____69951 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____69977 =
            let uu____69982 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____69983 =
              let uu____69984 =
                let uu____69993 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____69993  in
              let uu____69994 =
                let uu____70005 =
                  let uu____70014 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____70014  in
                let uu____70015 =
                  let uu____70026 =
                    let uu____70035 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____70035  in
                  [uu____70026]  in
                uu____70005 :: uu____70015  in
              uu____69984 :: uu____69994  in
            FStar_Syntax_Syntax.mk_Tm_app uu____69982 uu____69983  in
          uu____69977 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____70072 =
            let uu____70077 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____70078 =
              let uu____70079 =
                let uu____70088 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____70088  in
              let uu____70089 =
                let uu____70100 =
                  let uu____70109 = embed e_exn rng e  in
                  FStar_Syntax_Syntax.as_arg uu____70109  in
                let uu____70110 =
                  let uu____70121 =
                    let uu____70130 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____70130  in
                  [uu____70121]  in
                uu____70100 :: uu____70110  in
              uu____70079 :: uu____70089  in
            FStar_Syntax_Syntax.mk_Tm_app uu____70077 uu____70078  in
          uu____70072 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____70187 =
      let uu____70195 = hd'_and_args t  in
      match uu____70195 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____70217)::(ps,uu____70219)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____70286 = unembed' w ea a  in
          FStar_Util.bind_opt uu____70286
            (fun a1  ->
               let uu____70294 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____70294
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____70306)::(ps,uu____70308)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____70375 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____70375
            (fun e1  ->
               let uu____70383 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____70383
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____70392 ->
          (if w
           then
             (let uu____70409 =
                let uu____70415 =
                  let uu____70417 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____70417
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____70415)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____70409)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____70425 =
      let uu____70426 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____70426  in
    let uu____70427 =
      let uu____70428 =
        let uu____70436 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____70439 =
          let uu____70442 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____70442]  in
        (uu____70436, uu____70439)  in
      FStar_Syntax_Syntax.ET_app uu____70428  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____70425 (fun uu____70449  -> "") uu____70427
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____70489 =
            let uu____70496 =
              let uu____70501 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____70501  in
            let uu____70502 =
              let uu____70509 =
                let uu____70514 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____70514  in
              let uu____70515 =
                let uu____70522 =
                  let uu____70527 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____70527  in
                [uu____70522]  in
              uu____70509 :: uu____70515  in
            uu____70496 :: uu____70502  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____70489
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____70546 =
            let uu____70553 =
              let uu____70558 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____70558  in
            let uu____70559 =
              let uu____70566 =
                let uu____70571 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____70571  in
              let uu____70572 =
                let uu____70579 =
                  let uu____70584 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____70584  in
                [uu____70579]  in
              uu____70566 :: uu____70572  in
            uu____70553 :: uu____70559  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____70546
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____70621,(ps,uu____70623)::(a,uu____70625)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____70657 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____70657
            (fun a1  ->
               let uu____70665 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____70665
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____70675,(ps,uu____70677)::(e,uu____70679)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____70711 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____70711
            (fun e1  ->
               let uu____70719 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____70719
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____70728 -> FStar_Pervasives_Native.None  in
    let uu____70731 = mkFV fv_result [] []  in
    let uu____70736 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____70731;
      FStar_TypeChecker_NBETerm.emb_typ = uu____70736
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____70770 =
      let uu____70771 = FStar_Syntax_Subst.compress t  in
      uu____70771.FStar_Syntax_Syntax.n  in
    match uu____70770 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____70778 ->
        (if w
         then
           (let uu____70781 =
              let uu____70787 =
                let uu____70789 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s"
                  uu____70789
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____70787)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____70781)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____70833,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____70849,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____70864 ->
        ((let uu____70866 =
            let uu____70872 =
              let uu____70874 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____70874
               in
            (FStar_Errors.Warning_NotEmbedded, uu____70872)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____70866);
         FStar_Pervasives_Native.None)
     in
  let uu____70878 = mkFV fv_direction [] []  in
  let uu____70883 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____70878;
    FStar_TypeChecker_NBETerm.emb_typ = uu____70883
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
    let uu____70915 =
      let uu____70916 = FStar_Syntax_Subst.compress t  in
      uu____70916.FStar_Syntax_Syntax.n  in
    match uu____70915 with
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
    | uu____70925 ->
        (if w
         then
           (let uu____70928 =
              let uu____70934 =
                let uu____70936 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____70936
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____70934)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____70928)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____70990,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____71006,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____71022,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____71038,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____71053 -> FStar_Pervasives_Native.None  in
  let uu____71054 = mkFV fv_guard_policy [] []  in
  let uu____71059 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____71054;
    FStar_TypeChecker_NBETerm.emb_typ = uu____71059
  } 