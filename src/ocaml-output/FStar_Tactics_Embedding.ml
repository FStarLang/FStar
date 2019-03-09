open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____63667 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____63667 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____63676 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_tm uu____63676
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____63693 = lid_as_data_fv l  in
    FStar_Syntax_Syntax.fv_to_tm uu____63693
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____63702 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____63702
  
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
  let uu____63788 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____63788 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____63795 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____63795 
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____63802 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.tconst uu____63802 
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____63809 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.fvconst uu____63809 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____63823 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____63823 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____63837 =
      let uu____63848 = FStar_Syntax_Syntax.as_arg t  in [uu____63848]  in
    FStar_Syntax_Util.mk_app t_result uu____63837
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____63874 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____63874 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____63881 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____63881 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____63888 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____63888 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____63895 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____63895 
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
        let uu____63954 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____63954
  
let embed :
  'Auu____63981 .
    'Auu____63981 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____63981 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____64001 = FStar_Syntax_Embeddings.embed e x  in
        uu____64001 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____64019 .
    Prims.bool ->
      'Auu____64019 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____64019 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____64043 = FStar_Syntax_Embeddings.unembed e x  in
        uu____64043 w FStar_Syntax_Embeddings.id_norm_cb
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____64071 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____64071 with
    | (hd1,args) ->
        let uu____64128 =
          let uu____64129 = FStar_Syntax_Util.un_uinst hd1  in
          uu____64129.FStar_Syntax_Syntax.n  in
        (uu____64128, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____64173 =
      let uu____64174 = FStar_Syntax_Subst.compress t  in
      uu____64174.FStar_Syntax_Syntax.n  in
    match uu____64173 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____64180;
          FStar_Syntax_Syntax.rng = uu____64181;_}
        ->
        let uu____64184 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64187  -> FStar_Pervasives_Native.Some _64187) uu____64184
    | uu____64188 ->
        (if w
         then
           (let uu____64191 =
              let uu____64197 =
                let uu____64199 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s"
                  uu____64199
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64197)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64191)
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
    let uu____64290 =
      let uu____64298 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____64298, [])  in
    FStar_Syntax_Syntax.ET_app uu____64290
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____64318 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____64318;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____64323  ->
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
           FStar_Syntax_Syntax.ltyp = uu____64356;
           FStar_Syntax_Syntax.rng = uu____64357;_},uu____64358)
        ->
        let uu____64377 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64380  -> FStar_Pervasives_Native.Some _64380) uu____64377
    | uu____64381 ->
        ((let uu____64383 =
            let uu____64389 =
              let uu____64391 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____64391
               in
            (FStar_Errors.Warning_NotEmbedded, uu____64389)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64383);
         FStar_Pervasives_Native.None)
     in
  let uu____64395 = mkFV fv_proofstate [] []  in
  let uu____64400 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____64395;
    FStar_TypeChecker_NBETerm.emb_typ = uu____64400
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____64432 =
      let uu____64433 = FStar_Syntax_Subst.compress t  in
      uu____64433.FStar_Syntax_Syntax.n  in
    match uu____64432 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____64439;
          FStar_Syntax_Syntax.rng = uu____64440;_}
        ->
        let uu____64443 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64446  -> FStar_Pervasives_Native.Some _64446) uu____64443
    | uu____64447 ->
        (if w
         then
           (let uu____64450 =
              let uu____64456 =
                let uu____64458 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____64458  in
              (FStar_Errors.Warning_NotEmbedded, uu____64456)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64450)
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
      let uu____64486 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____64486;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____64491  ->
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
           FStar_Syntax_Syntax.ltyp = uu____64524;
           FStar_Syntax_Syntax.rng = uu____64525;_},uu____64526)
        ->
        let uu____64545 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64548  -> FStar_Pervasives_Native.Some _64548) uu____64545
    | uu____64549 ->
        ((let uu____64551 =
            let uu____64557 =
              let uu____64559 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE goal: %s" uu____64559
               in
            (FStar_Errors.Warning_NotEmbedded, uu____64557)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64551);
         FStar_Pervasives_Native.None)
     in
  let uu____64563 = mkFV fv_goal [] []  in
  let uu____64568 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____64563;
    FStar_TypeChecker_NBETerm.emb_typ = uu____64568
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____64594 uu____64595 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____64599 =
          let uu____64604 =
            let uu____64605 =
              let uu____64614 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____64614  in
            [uu____64605]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____64604
           in
        uu____64599 FStar_Pervasives_Native.None rng
    | FStar_Tactics_Types.EExn t ->
        let uu___726_64633 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___726_64633.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___726_64633.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____64637 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____64637  in
        let uu____64640 =
          let uu____64645 =
            let uu____64646 =
              let uu____64655 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____64655  in
            [uu____64646]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____64645
           in
        uu____64640 FStar_Pervasives_Native.None rng
     in
  let unembed_exn t w uu____64692 =
    let uu____64697 = hd'_and_args t  in
    match uu____64697 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____64716)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____64751 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____64751
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____64760 ->
        FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____64775 =
    let uu____64776 =
      let uu____64784 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____64784, [])  in
    FStar_Syntax_Syntax.ET_app uu____64776  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____64791  -> "(exn)") uu____64775
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____64809 =
          let uu____64816 =
            let uu____64821 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____64821  in
          [uu____64816]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____64809
    | uu____64831 ->
        let uu____64832 =
          let uu____64834 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____64834  in
        failwith uu____64832
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____64853,(s,uu____64855)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____64874 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____64874
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____64883 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____64885 = mkFV fv_exn [] []  in
  let uu____64890 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____64885;
    FStar_TypeChecker_NBETerm.emb_typ = uu____64890
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____64932 uu____64933 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____64939 =
            let uu____64944 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____64945 =
              let uu____64946 =
                let uu____64955 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____64955  in
              let uu____64956 =
                let uu____64967 =
                  let uu____64976 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____64976  in
                let uu____64977 =
                  let uu____64988 =
                    let uu____64997 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____64997  in
                  [uu____64988]  in
                uu____64967 :: uu____64977  in
              uu____64946 :: uu____64956  in
            FStar_Syntax_Syntax.mk_Tm_app uu____64944 uu____64945  in
          uu____64939 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____65032 =
            let uu____65037 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____65038 =
              let uu____65039 =
                let uu____65048 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____65048  in
              let uu____65049 =
                let uu____65060 =
                  let uu____65069 = embed e_exn rng e  in
                  FStar_Syntax_Syntax.as_arg uu____65069  in
                let uu____65070 =
                  let uu____65081 =
                    let uu____65090 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____65090  in
                  [uu____65081]  in
                uu____65060 :: uu____65070  in
              uu____65039 :: uu____65049  in
            FStar_Syntax_Syntax.mk_Tm_app uu____65037 uu____65038  in
          uu____65032 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____65144 =
      let uu____65151 = hd'_and_args t  in
      match uu____65151 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____65173)::(ps,uu____65175)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____65242 = unembed' w ea a  in
          FStar_Util.bind_opt uu____65242
            (fun a1  ->
               let uu____65250 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____65250
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____65262)::(ps,uu____65264)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____65331 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____65331
            (fun e1  ->
               let uu____65339 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____65339
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____65348 ->
          (if w
           then
             (let uu____65365 =
                let uu____65371 =
                  let uu____65373 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____65373
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____65371)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65365)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____65381 =
      let uu____65382 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____65382  in
    let uu____65383 =
      let uu____65384 =
        let uu____65392 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____65395 =
          let uu____65398 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____65398]  in
        (uu____65392, uu____65395)  in
      FStar_Syntax_Syntax.ET_app uu____65384  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____65381 (fun uu____65405  -> "") uu____65383
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____65445 =
            let uu____65452 =
              let uu____65457 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____65457  in
            let uu____65458 =
              let uu____65465 =
                let uu____65470 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____65470  in
              let uu____65471 =
                let uu____65478 =
                  let uu____65483 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____65483  in
                [uu____65478]  in
              uu____65465 :: uu____65471  in
            uu____65452 :: uu____65458  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____65445
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____65502 =
            let uu____65509 =
              let uu____65514 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____65514  in
            let uu____65515 =
              let uu____65522 =
                let uu____65527 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____65527  in
              let uu____65528 =
                let uu____65535 =
                  let uu____65540 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____65540  in
                [uu____65535]  in
              uu____65522 :: uu____65528  in
            uu____65509 :: uu____65515  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____65502
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____65577,(ps,uu____65579)::(a,uu____65581)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____65613 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____65613
            (fun a1  ->
               let uu____65621 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____65621
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____65631,(ps,uu____65633)::(e,uu____65635)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____65667 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____65667
            (fun e1  ->
               let uu____65675 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____65675
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____65684 -> FStar_Pervasives_Native.None  in
    let uu____65687 = mkFV fv_result [] []  in
    let uu____65692 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____65687;
      FStar_TypeChecker_NBETerm.emb_typ = uu____65692
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____65726 =
      let uu____65727 = FStar_Syntax_Subst.compress t  in
      uu____65727.FStar_Syntax_Syntax.n  in
    match uu____65726 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____65734 ->
        (if w
         then
           (let uu____65737 =
              let uu____65743 =
                let uu____65745 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s"
                  uu____65745
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65743)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65737)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65789,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65805,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____65820 ->
        ((let uu____65822 =
            let uu____65828 =
              let uu____65830 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____65830
               in
            (FStar_Errors.Warning_NotEmbedded, uu____65828)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65822);
         FStar_Pervasives_Native.None)
     in
  let uu____65834 = mkFV fv_direction [] []  in
  let uu____65839 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____65834;
    FStar_TypeChecker_NBETerm.emb_typ = uu____65839
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
    let uu____65871 =
      let uu____65872 = FStar_Syntax_Subst.compress t  in
      uu____65872.FStar_Syntax_Syntax.n  in
    match uu____65871 with
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
    | uu____65881 ->
        (if w
         then
           (let uu____65884 =
              let uu____65890 =
                let uu____65892 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____65892
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65890)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65884)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65946,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65962,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65978,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65994,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____66009 -> FStar_Pervasives_Native.None  in
  let uu____66010 = mkFV fv_guard_policy [] []  in
  let uu____66015 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____66010;
    FStar_TypeChecker_NBETerm.emb_typ = uu____66015
  } 