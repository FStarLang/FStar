open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____63686 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____63686 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____63695 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_tm uu____63695
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____63712 = lid_as_data_fv l  in
    FStar_Syntax_Syntax.fv_to_tm uu____63712
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____63721 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____63721
  
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
  let uu____63807 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____63807 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____63814 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____63814 
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____63821 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.tconst uu____63821 
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____63828 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.fvconst uu____63828 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____63842 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____63842 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____63856 =
      let uu____63867 = FStar_Syntax_Syntax.as_arg t  in [uu____63867]  in
    FStar_Syntax_Util.mk_app t_result uu____63856
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____63893 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____63893 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____63900 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____63900 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____63907 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____63907 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____63914 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____63914 
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
        let uu____63973 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____63973
  
let embed :
  'Auu____64000 .
    'Auu____64000 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____64000 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____64020 = FStar_Syntax_Embeddings.embed e x  in
        uu____64020 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____64038 .
    Prims.bool ->
      'Auu____64038 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____64038 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____64062 = FStar_Syntax_Embeddings.unembed e x  in
        uu____64062 w FStar_Syntax_Embeddings.id_norm_cb
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____64090 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____64090 with
    | (hd1,args) ->
        let uu____64147 =
          let uu____64148 = FStar_Syntax_Util.un_uinst hd1  in
          uu____64148.FStar_Syntax_Syntax.n  in
        (uu____64147, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____64192 =
      let uu____64193 = FStar_Syntax_Subst.compress t  in
      uu____64193.FStar_Syntax_Syntax.n  in
    match uu____64192 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____64199;
          FStar_Syntax_Syntax.rng = uu____64200;_}
        ->
        let uu____64203 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64206  -> FStar_Pervasives_Native.Some _64206) uu____64203
    | uu____64207 ->
        (if w
         then
           (let uu____64210 =
              let uu____64216 =
                let uu____64218 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s"
                  uu____64218
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64216)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64210)
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
    let uu____64309 =
      let uu____64317 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____64317, [])  in
    FStar_Syntax_Syntax.ET_app uu____64309
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____64337 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____64337;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____64342  ->
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
           FStar_Syntax_Syntax.ltyp = uu____64375;
           FStar_Syntax_Syntax.rng = uu____64376;_},uu____64377)
        ->
        let uu____64396 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64399  -> FStar_Pervasives_Native.Some _64399) uu____64396
    | uu____64400 ->
        ((let uu____64402 =
            let uu____64408 =
              let uu____64410 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____64410
               in
            (FStar_Errors.Warning_NotEmbedded, uu____64408)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64402);
         FStar_Pervasives_Native.None)
     in
  let uu____64414 = mkFV fv_proofstate [] []  in
  let uu____64419 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____64414;
    FStar_TypeChecker_NBETerm.emb_typ = uu____64419
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____64451 =
      let uu____64452 = FStar_Syntax_Subst.compress t  in
      uu____64452.FStar_Syntax_Syntax.n  in
    match uu____64451 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____64458;
          FStar_Syntax_Syntax.rng = uu____64459;_}
        ->
        let uu____64462 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64465  -> FStar_Pervasives_Native.Some _64465) uu____64462
    | uu____64466 ->
        (if w
         then
           (let uu____64469 =
              let uu____64475 =
                let uu____64477 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____64477  in
              (FStar_Errors.Warning_NotEmbedded, uu____64475)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64469)
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
      let uu____64505 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____64505;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____64510  ->
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
           FStar_Syntax_Syntax.ltyp = uu____64543;
           FStar_Syntax_Syntax.rng = uu____64544;_},uu____64545)
        ->
        let uu____64564 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64567  -> FStar_Pervasives_Native.Some _64567) uu____64564
    | uu____64568 ->
        ((let uu____64570 =
            let uu____64576 =
              let uu____64578 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE goal: %s" uu____64578
               in
            (FStar_Errors.Warning_NotEmbedded, uu____64576)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64570);
         FStar_Pervasives_Native.None)
     in
  let uu____64582 = mkFV fv_goal [] []  in
  let uu____64587 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____64582;
    FStar_TypeChecker_NBETerm.emb_typ = uu____64587
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____64613 uu____64614 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____64618 =
          let uu____64623 =
            let uu____64624 =
              let uu____64633 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____64633  in
            [uu____64624]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____64623
           in
        uu____64618 FStar_Pervasives_Native.None rng
    | FStar_Tactics_Types.EExn t ->
        let uu___726_64652 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___726_64652.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___726_64652.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____64656 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____64656  in
        let uu____64659 =
          let uu____64664 =
            let uu____64665 =
              let uu____64674 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____64674  in
            [uu____64665]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____64664
           in
        uu____64659 FStar_Pervasives_Native.None rng
     in
  let unembed_exn t w uu____64711 =
    let uu____64716 = hd'_and_args t  in
    match uu____64716 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____64735)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____64770 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____64770
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____64779 ->
        FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____64794 =
    let uu____64795 =
      let uu____64803 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____64803, [])  in
    FStar_Syntax_Syntax.ET_app uu____64795  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____64810  -> "(exn)") uu____64794
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____64828 =
          let uu____64835 =
            let uu____64840 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____64840  in
          [uu____64835]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____64828
    | uu____64850 ->
        let uu____64851 =
          let uu____64853 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____64853  in
        failwith uu____64851
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____64872,(s,uu____64874)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____64893 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____64893
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____64902 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____64904 = mkFV fv_exn [] []  in
  let uu____64909 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____64904;
    FStar_TypeChecker_NBETerm.emb_typ = uu____64909
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____64951 uu____64952 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____64958 =
            let uu____64963 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____64964 =
              let uu____64965 =
                let uu____64974 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____64974  in
              let uu____64975 =
                let uu____64986 =
                  let uu____64995 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____64995  in
                let uu____64996 =
                  let uu____65007 =
                    let uu____65016 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____65016  in
                  [uu____65007]  in
                uu____64986 :: uu____64996  in
              uu____64965 :: uu____64975  in
            FStar_Syntax_Syntax.mk_Tm_app uu____64963 uu____64964  in
          uu____64958 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____65051 =
            let uu____65056 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____65057 =
              let uu____65058 =
                let uu____65067 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____65067  in
              let uu____65068 =
                let uu____65079 =
                  let uu____65088 = embed e_exn rng e  in
                  FStar_Syntax_Syntax.as_arg uu____65088  in
                let uu____65089 =
                  let uu____65100 =
                    let uu____65109 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____65109  in
                  [uu____65100]  in
                uu____65079 :: uu____65089  in
              uu____65058 :: uu____65068  in
            FStar_Syntax_Syntax.mk_Tm_app uu____65056 uu____65057  in
          uu____65051 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____65163 =
      let uu____65170 = hd'_and_args t  in
      match uu____65170 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____65192)::(ps,uu____65194)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____65261 = unembed' w ea a  in
          FStar_Util.bind_opt uu____65261
            (fun a1  ->
               let uu____65269 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____65269
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____65281)::(ps,uu____65283)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____65350 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____65350
            (fun e1  ->
               let uu____65358 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____65358
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____65367 ->
          (if w
           then
             (let uu____65384 =
                let uu____65390 =
                  let uu____65392 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____65392
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____65390)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65384)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____65400 =
      let uu____65401 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____65401  in
    let uu____65402 =
      let uu____65403 =
        let uu____65411 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____65414 =
          let uu____65417 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____65417]  in
        (uu____65411, uu____65414)  in
      FStar_Syntax_Syntax.ET_app uu____65403  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____65400 (fun uu____65424  -> "") uu____65402
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____65464 =
            let uu____65471 =
              let uu____65476 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____65476  in
            let uu____65477 =
              let uu____65484 =
                let uu____65489 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____65489  in
              let uu____65490 =
                let uu____65497 =
                  let uu____65502 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____65502  in
                [uu____65497]  in
              uu____65484 :: uu____65490  in
            uu____65471 :: uu____65477  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____65464
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____65521 =
            let uu____65528 =
              let uu____65533 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____65533  in
            let uu____65534 =
              let uu____65541 =
                let uu____65546 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____65546  in
              let uu____65547 =
                let uu____65554 =
                  let uu____65559 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____65559  in
                [uu____65554]  in
              uu____65541 :: uu____65547  in
            uu____65528 :: uu____65534  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____65521
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____65596,(ps,uu____65598)::(a,uu____65600)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____65632 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____65632
            (fun a1  ->
               let uu____65640 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____65640
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____65650,(ps,uu____65652)::(e,uu____65654)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____65686 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____65686
            (fun e1  ->
               let uu____65694 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____65694
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____65703 -> FStar_Pervasives_Native.None  in
    let uu____65706 = mkFV fv_result [] []  in
    let uu____65711 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____65706;
      FStar_TypeChecker_NBETerm.emb_typ = uu____65711
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____65745 =
      let uu____65746 = FStar_Syntax_Subst.compress t  in
      uu____65746.FStar_Syntax_Syntax.n  in
    match uu____65745 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____65753 ->
        (if w
         then
           (let uu____65756 =
              let uu____65762 =
                let uu____65764 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s"
                  uu____65764
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65762)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65756)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65808,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65824,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____65839 ->
        ((let uu____65841 =
            let uu____65847 =
              let uu____65849 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____65849
               in
            (FStar_Errors.Warning_NotEmbedded, uu____65847)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65841);
         FStar_Pervasives_Native.None)
     in
  let uu____65853 = mkFV fv_direction [] []  in
  let uu____65858 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____65853;
    FStar_TypeChecker_NBETerm.emb_typ = uu____65858
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
    let uu____65890 =
      let uu____65891 = FStar_Syntax_Subst.compress t  in
      uu____65891.FStar_Syntax_Syntax.n  in
    match uu____65890 with
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
    | uu____65900 ->
        (if w
         then
           (let uu____65903 =
              let uu____65909 =
                let uu____65911 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____65911
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65909)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65903)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65965,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65981,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____65997,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____66013,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____66028 -> FStar_Pervasives_Native.None  in
  let uu____66029 = mkFV fv_guard_policy [] []  in
  let uu____66034 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____66029;
    FStar_TypeChecker_NBETerm.emb_typ = uu____66034
  } 