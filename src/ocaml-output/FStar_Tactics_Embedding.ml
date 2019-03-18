open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____63653 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____63653 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____63662 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_tm uu____63662
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____63679 = lid_as_data_fv l  in
    FStar_Syntax_Syntax.fv_to_tm uu____63679
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____63688 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____63688
  
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
  let uu____63774 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____63774 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____63781 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____63781 
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____63788 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.tconst uu____63788 
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____63795 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.fvconst uu____63795 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____63809 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____63809 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____63823 =
      let uu____63834 = FStar_Syntax_Syntax.as_arg t  in [uu____63834]  in
    FStar_Syntax_Util.mk_app t_result uu____63823
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____63860 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____63860 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____63867 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____63867 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____63874 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____63874 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____63881 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____63881 
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
        let uu____63940 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____63940
  
let embed :
  'Auu____63967 .
    'Auu____63967 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____63967 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____63987 = FStar_Syntax_Embeddings.embed e x  in
        uu____63987 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____64005 .
    Prims.bool ->
      'Auu____64005 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____64005 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____64029 = FStar_Syntax_Embeddings.unembed e x  in
        uu____64029 w FStar_Syntax_Embeddings.id_norm_cb
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____64057 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____64057 with
    | (hd1,args) ->
        let uu____64114 =
          let uu____64115 = FStar_Syntax_Util.un_uinst hd1  in
          uu____64115.FStar_Syntax_Syntax.n  in
        (uu____64114, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____64159 =
      let uu____64160 = FStar_Syntax_Subst.compress t  in
      uu____64160.FStar_Syntax_Syntax.n  in
    match uu____64159 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____64166;
          FStar_Syntax_Syntax.rng = uu____64167;_}
        ->
        let uu____64170 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64173  -> FStar_Pervasives_Native.Some _64173) uu____64170
    | uu____64174 ->
        (if w
         then
           (let uu____64177 =
              let uu____64183 =
                let uu____64185 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s"
                  uu____64185
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64183)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64177)
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
    let uu____64276 =
      let uu____64284 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____64284, [])  in
    FStar_Syntax_Syntax.ET_app uu____64276
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____64304 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____64304;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____64309  ->
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
           FStar_Syntax_Syntax.ltyp = uu____64342;
           FStar_Syntax_Syntax.rng = uu____64343;_},uu____64344)
        ->
        let uu____64363 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64366  -> FStar_Pervasives_Native.Some _64366) uu____64363
    | uu____64367 ->
        ((let uu____64369 =
            let uu____64375 =
              let uu____64377 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____64377
               in
            (FStar_Errors.Warning_NotEmbedded, uu____64375)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64369);
         FStar_Pervasives_Native.None)
     in
  let uu____64381 = mkFV fv_proofstate [] []  in
  let uu____64386 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____64381;
    FStar_TypeChecker_NBETerm.emb_typ = uu____64386
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____64418 =
      let uu____64419 = FStar_Syntax_Subst.compress t  in
      uu____64419.FStar_Syntax_Syntax.n  in
    match uu____64418 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____64425;
          FStar_Syntax_Syntax.rng = uu____64426;_}
        ->
        let uu____64429 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64432  -> FStar_Pervasives_Native.Some _64432) uu____64429
    | uu____64433 ->
        (if w
         then
           (let uu____64436 =
              let uu____64442 =
                let uu____64444 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____64444  in
              (FStar_Errors.Warning_NotEmbedded, uu____64442)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64436)
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
      let uu____64472 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____64472;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____64477  ->
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
           FStar_Syntax_Syntax.ltyp = uu____64510;
           FStar_Syntax_Syntax.rng = uu____64511;_},uu____64512)
        ->
        let uu____64531 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64534  -> FStar_Pervasives_Native.Some _64534) uu____64531
    | uu____64535 ->
        ((let uu____64537 =
            let uu____64543 =
              let uu____64545 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE goal: %s" uu____64545
               in
            (FStar_Errors.Warning_NotEmbedded, uu____64543)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64537);
         FStar_Pervasives_Native.None)
     in
  let uu____64549 = mkFV fv_goal [] []  in
  let uu____64554 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____64549;
    FStar_TypeChecker_NBETerm.emb_typ = uu____64554
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____64580 uu____64581 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____64585 =
          let uu____64590 =
            let uu____64591 =
              let uu____64600 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____64600  in
            [uu____64591]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____64590
           in
        uu____64585 FStar_Pervasives_Native.None rng
    | FStar_Tactics_Types.EExn t ->
        let uu___726_64619 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___726_64619.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___726_64619.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____64623 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____64623  in
        let uu____64626 =
          let uu____64631 =
            let uu____64632 =
              let uu____64641 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____64641  in
            [uu____64632]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____64631
           in
        uu____64626 FStar_Pervasives_Native.None rng
     in
  let unembed_exn t w uu____64678 =
    let uu____64683 = hd'_and_args t  in
    match uu____64683 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____64702)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____64737 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____64737
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____64746 ->
        FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____64761 =
    let uu____64762 =
      let uu____64770 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____64770, [])  in
    FStar_Syntax_Syntax.ET_app uu____64762  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____64777  -> "(exn)") uu____64761
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____64795 =
          let uu____64802 =
            let uu____64807 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____64807  in
          [uu____64802]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____64795
    | uu____64817 ->
        let uu____64818 =
          let uu____64820 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____64820  in
        failwith uu____64818
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____64839,(s,uu____64841)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____64860 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____64860
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____64869 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____64871 = mkFV fv_exn [] []  in
  let uu____64876 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____64871;
    FStar_TypeChecker_NBETerm.emb_typ = uu____64876
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____64918 uu____64919 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____64925 =
            let uu____64930 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____64931 =
              let uu____64932 =
                let uu____64941 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____64941  in
              let uu____64942 =
                let uu____64953 =
                  let uu____64962 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____64962  in
                let uu____64963 =
                  let uu____64974 =
                    let uu____64983 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____64983  in
                  [uu____64974]  in
                uu____64953 :: uu____64963  in
              uu____64932 :: uu____64942  in
            FStar_Syntax_Syntax.mk_Tm_app uu____64930 uu____64931  in
          uu____64925 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____65018 =
            let uu____65023 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____65024 =
              let uu____65025 =
                let uu____65034 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____65034  in
              let uu____65035 =
                let uu____65046 =
                  let uu____65055 = embed e_exn rng e  in
                  FStar_Syntax_Syntax.as_arg uu____65055  in
                let uu____65056 =
                  let uu____65067 =
                    let uu____65076 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____65076  in
                  [uu____65067]  in
                uu____65046 :: uu____65056  in
              uu____65025 :: uu____65035  in
            FStar_Syntax_Syntax.mk_Tm_app uu____65023 uu____65024  in
          uu____65018 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____65130 =
      let uu____65137 = hd'_and_args t  in
      match uu____65137 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____65159)::(ps,uu____65161)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____65228 = unembed' w ea a  in
          FStar_Util.bind_opt uu____65228
            (fun a1  ->
               let uu____65236 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____65236
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____65248)::(ps,uu____65250)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____65317 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____65317
            (fun e1  ->
               let uu____65325 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____65325
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____65334 ->
          (if w
           then
             (let uu____65351 =
                let uu____65357 =
                  let uu____65359 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____65359
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____65357)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65351)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____65367 =
      let uu____65368 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____65368  in
    let uu____65369 =
      let uu____65370 =
        let uu____65378 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____65381 =
          let uu____65384 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____65384]  in
        (uu____65378, uu____65381)  in
      FStar_Syntax_Syntax.ET_app uu____65370  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____65367 (fun uu____65391  -> "") uu____65369
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____65431 =
            let uu____65438 =
              let uu____65443 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____65443  in
            let uu____65444 =
              let uu____65451 =
                let uu____65456 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____65456  in
              let uu____65457 =
                let uu____65464 =
                  let uu____65469 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____65469  in
                [uu____65464]  in
              uu____65451 :: uu____65457  in
            uu____65438 :: uu____65444  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____65431
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____65488 =
            let uu____65495 =
              let uu____65500 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____65500  in
            let uu____65501 =
              let uu____65508 =
                let uu____65513 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____65513  in
              let uu____65514 =
                let uu____65521 =
                  let uu____65526 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____65526  in
                [uu____65521]  in
              uu____65508 :: uu____65514  in
            uu____65495 :: uu____65501  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____65488
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____65563,(ps,uu____65565)::(a,uu____65567)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____65599 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____65599
            (fun a1  ->
               let uu____65607 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____65607
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____65617,(ps,uu____65619)::(e,uu____65621)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____65653 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____65653
            (fun e1  ->
               let uu____65661 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____65661
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____65670 -> FStar_Pervasives_Native.None  in
    let uu____65673 = mkFV fv_result [] []  in
    let uu____65678 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____65673;
      FStar_TypeChecker_NBETerm.emb_typ = uu____65678
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____65712 =
      let uu____65713 = FStar_Syntax_Subst.compress t  in
      uu____65713.FStar_Syntax_Syntax.n  in
    match uu____65712 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____65720 ->
        (if w
         then
           (let uu____65723 =
              let uu____65729 =
                let uu____65731 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s"
                  uu____65731
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65729)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65723)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65775,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65791,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____65806 ->
        ((let uu____65808 =
            let uu____65814 =
              let uu____65816 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____65816
               in
            (FStar_Errors.Warning_NotEmbedded, uu____65814)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65808);
         FStar_Pervasives_Native.None)
     in
  let uu____65820 = mkFV fv_direction [] []  in
  let uu____65825 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____65820;
    FStar_TypeChecker_NBETerm.emb_typ = uu____65825
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
    let uu____65857 =
      let uu____65858 = FStar_Syntax_Subst.compress t  in
      uu____65858.FStar_Syntax_Syntax.n  in
    match uu____65857 with
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
    | uu____65867 ->
        (if w
         then
           (let uu____65870 =
              let uu____65876 =
                let uu____65878 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____65878
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65876)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65870)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65932,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65948,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65964,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65980,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____65995 -> FStar_Pervasives_Native.None  in
  let uu____65996 = mkFV fv_guard_policy [] []  in
  let uu____66001 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____65996;
    FStar_TypeChecker_NBETerm.emb_typ = uu____66001
  } 