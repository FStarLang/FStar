open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____17 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____17 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____26 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____26
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____43 = lid_as_data_fv l  in FStar_Syntax_Syntax.fv_to_tm uu____43
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____52 = fstar_tactics_lid' ["Effect"; s]  in
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
let (fstar_tactics_Continue_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Continue"] 
let (fstar_tactics_Skip_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Skip"] 
let (fstar_tactics_Abort_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Types"; "Abort"] 
let (fstar_tactics_Continue : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Continue_lid 
let (fstar_tactics_Skip : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Skip_lid 
let (fstar_tactics_Abort : FStar_Syntax_Syntax.term) =
  lid_as_data_tm fstar_tactics_Abort_lid 
let (fstar_tactics_Continue_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Continue_lid 
let (fstar_tactics_Skip_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Skip_lid 
let (fstar_tactics_Abort_fv : FStar_Syntax_Syntax.fv) =
  lid_as_data_fv fstar_tactics_Abort_lid 
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
  let uu____162 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____162 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____169 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____169 
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____176 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.tconst uu____176 
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____183 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.fvconst uu____183 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____197 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____197 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____211 =
      let uu____222 = FStar_Syntax_Syntax.as_arg t  in [uu____222]  in
    FStar_Syntax_Util.mk_app t_result uu____211
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____248 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____248 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____255 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____255 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____262 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____262 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____269 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____269 
let (t_ctrl_flag : FStar_Syntax_Syntax.term) =
  let uu____276 = fstar_tactics_lid' ["Types"; "ctrl_flag"]  in
  FStar_Syntax_Syntax.tconst uu____276 
let (fv_ctrl_flag : FStar_Syntax_Syntax.fv) =
  let uu____283 = fstar_tactics_lid' ["Types"; "ctrl_flag"]  in
  FStar_Syntax_Syntax.fvconst uu____283 
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
        let uu____342 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____342
  
let embed :
  'Auu____369 .
    'Auu____369 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____369 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____389 = FStar_Syntax_Embeddings.embed e x  in
        uu____389 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____407 .
    Prims.bool ->
      'Auu____407 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____407 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____431 = FStar_Syntax_Embeddings.unembed e x  in
        uu____431 w FStar_Syntax_Embeddings.id_norm_cb
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____459 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____459 with
    | (hd1,args) ->
        let uu____516 =
          let uu____517 = FStar_Syntax_Util.un_uinst hd1  in
          uu____517.FStar_Syntax_Syntax.n  in
        (uu____516, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____561 =
      let uu____562 = FStar_Syntax_Subst.compress t  in
      uu____562.FStar_Syntax_Syntax.n  in
    match uu____561 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____568;
          FStar_Syntax_Syntax.rng = uu____569;_}
        ->
        let uu____572 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _575  -> FStar_Pervasives_Native.Some _575)
          uu____572
    | uu____576 ->
        (if w
         then
           (let uu____579 =
              let uu____585 =
                let uu____587 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s\n"
                  uu____587
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____585)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____579)
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
    let uu____678 =
      let uu____686 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____686, [])  in
    FStar_Syntax_Syntax.ET_app uu____678
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____706 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____706;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Thunk.mk
        (fun uu____711  ->
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
           FStar_Syntax_Syntax.ltyp = uu____744;
           FStar_Syntax_Syntax.rng = uu____745;_},uu____746)
        ->
        let uu____765 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _768  -> FStar_Pervasives_Native.Some _768)
          uu____765
    | uu____769 ->
        ((let uu____771 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____771
          then
            let uu____795 =
              let uu____801 =
                let uu____803 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded NBE proofstate: %s\n"
                  uu____803
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____801)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____795
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____809 = mkFV fv_proofstate [] []  in
  let uu____814 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____809;
    FStar_TypeChecker_NBETerm.emb_typ = uu____814
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____846 =
      let uu____847 = FStar_Syntax_Subst.compress t  in
      uu____847.FStar_Syntax_Syntax.n  in
    match uu____846 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____853;
          FStar_Syntax_Syntax.rng = uu____854;_}
        ->
        let uu____857 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _860  -> FStar_Pervasives_Native.Some _860)
          uu____857
    | uu____861 ->
        (if w
         then
           (let uu____864 =
              let uu____870 =
                let uu____872 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____872  in
              (FStar_Errors.Warning_NotEmbedded, uu____870)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____864)
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
      let uu____900 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____900;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Thunk.mk
        (fun uu____905  ->
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
           FStar_Syntax_Syntax.ltyp = uu____938;
           FStar_Syntax_Syntax.rng = uu____939;_},uu____940)
        ->
        let uu____959 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _962  -> FStar_Pervasives_Native.Some _962)
          uu____959
    | uu____963 ->
        ((let uu____965 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____965
          then
            let uu____989 =
              let uu____995 =
                let uu____997 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded NBE goal: %s" uu____997
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____995)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____989
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____1003 = mkFV fv_goal [] []  in
  let uu____1008 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____1003;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1008
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____1034 uu____1035 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1039 =
          let uu____1044 =
            let uu____1045 =
              let uu____1054 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____1054  in
            [uu____1045]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____1044
           in
        uu____1039 FStar_Pervasives_Native.None rng
    | FStar_Tactics_Types.EExn t ->
        let uu___119_1073 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___119_1073.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___119_1073.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____1077 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____1077  in
        let uu____1080 =
          let uu____1085 =
            let uu____1086 =
              let uu____1095 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____1095  in
            [uu____1086]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____1085
           in
        uu____1080 FStar_Pervasives_Native.None rng
     in
  let unembed_exn t w uu____1132 =
    let uu____1137 = hd'_and_args t  in
    match uu____1137 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1156)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____1191 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____1191
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1200 -> FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____1215 =
    let uu____1216 =
      let uu____1224 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____1224, [])  in
    FStar_Syntax_Syntax.ET_app uu____1216  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____1231  -> "(exn)") uu____1215
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1249 =
          let uu____1256 =
            let uu____1261 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____1261  in
          [uu____1256]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____1249
    | uu____1271 ->
        let uu____1272 =
          let uu____1274 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____1274  in
        failwith uu____1272
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1293,(s,uu____1295)::[])
        when FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid
        ->
        let uu____1314 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1314
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1323 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____1325 = mkFV fv_exn [] []  in
  let uu____1330 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____1325;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1330
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____1372 uu____1373 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1379 =
            let uu____1384 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____1385 =
              let uu____1386 =
                let uu____1395 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____1395  in
              let uu____1396 =
                let uu____1407 =
                  let uu____1416 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1416  in
                let uu____1417 =
                  let uu____1428 =
                    let uu____1437 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____1437  in
                  [uu____1428]  in
                uu____1407 :: uu____1417  in
              uu____1386 :: uu____1396  in
            FStar_Syntax_Syntax.mk_Tm_app uu____1384 uu____1385  in
          uu____1379 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1472 =
            let uu____1477 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____1478 =
              let uu____1479 =
                let uu____1488 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____1488  in
              let uu____1489 =
                let uu____1500 =
                  let uu____1509 = embed e_exn rng e  in
                  FStar_Syntax_Syntax.as_arg uu____1509  in
                let uu____1510 =
                  let uu____1521 =
                    let uu____1530 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____1530  in
                  [uu____1521]  in
                uu____1500 :: uu____1510  in
              uu____1479 :: uu____1489  in
            FStar_Syntax_Syntax.mk_Tm_app uu____1477 uu____1478  in
          uu____1472 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____1584 =
      let uu____1591 = hd'_and_args t  in
      match uu____1591 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____1613)::(ps,uu____1615)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1682 = unembed' w ea a  in
          FStar_Util.bind_opt uu____1682
            (fun a1  ->
               let uu____1690 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1690
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____1702)::(ps,uu____1704)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1771 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____1771
            (fun e1  ->
               let uu____1779 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1779
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1788 ->
          (if w
           then
             (let uu____1805 =
                let uu____1811 =
                  let uu____1813 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1813
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____1811)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1805)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____1821 =
      let uu____1822 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____1822  in
    let uu____1823 =
      let uu____1824 =
        let uu____1832 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____1835 =
          let uu____1838 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____1838]  in
        (uu____1832, uu____1835)  in
      FStar_Syntax_Syntax.ET_app uu____1824  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1821 (fun uu____1845  -> "") uu____1823
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1885 =
            let uu____1892 =
              let uu____1897 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1897  in
            let uu____1898 =
              let uu____1905 =
                let uu____1910 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____1910  in
              let uu____1911 =
                let uu____1918 =
                  let uu____1923 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1923  in
                [uu____1918]  in
              uu____1905 :: uu____1911  in
            uu____1892 :: uu____1898  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____1885
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1942 =
            let uu____1949 =
              let uu____1954 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1954  in
            let uu____1955 =
              let uu____1962 =
                let uu____1967 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1967  in
              let uu____1968 =
                let uu____1975 =
                  let uu____1980 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1980  in
                [uu____1975]  in
              uu____1962 :: uu____1968  in
            uu____1949 :: uu____1955  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____1942
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2017,(ps,uu____2019)::(a,uu____2021)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____2053 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____2053
            (fun a1  ->
               let uu____2061 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____2061
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2071,(ps,uu____2073)::(e,uu____2075)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____2107 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____2107
            (fun e1  ->
               let uu____2115 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____2115
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____2124 -> FStar_Pervasives_Native.None  in
    let uu____2127 = mkFV fv_result [] []  in
    let uu____2132 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____2127;
      FStar_TypeChecker_NBETerm.emb_typ = uu____2132
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____2166 =
      let uu____2167 = FStar_Syntax_Subst.compress t  in
      uu____2167.FStar_Syntax_Syntax.n  in
    match uu____2166 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2174 ->
        (if w
         then
           (let uu____2177 =
              let uu____2183 =
                let uu____2185 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2185
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2183)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2177)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2229,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2245,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2260 ->
        ((let uu____2262 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____2262
          then
            let uu____2286 =
              let uu____2292 =
                let uu____2294 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2294
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2292)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2286
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____2300 = mkFV fv_direction [] []  in
  let uu____2305 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____2300;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2305
  } 
let (e_ctrl_flag :
  FStar_Tactics_Types.ctrl_flag FStar_Syntax_Embeddings.embedding) =
  let embed_ctrl_flag rng d =
    match d with
    | FStar_Tactics_Types.Continue  -> fstar_tactics_Continue
    | FStar_Tactics_Types.Skip  -> fstar_tactics_Skip
    | FStar_Tactics_Types.Abort  -> fstar_tactics_Abort  in
  let unembed_ctrl_flag w t =
    let uu____2337 =
      let uu____2338 = FStar_Syntax_Subst.compress t  in
      uu____2338.FStar_Syntax_Syntax.n  in
    match uu____2337 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2346 ->
        (if w
         then
           (let uu____2349 =
              let uu____2355 =
                let uu____2357 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2357
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2355)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2349)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_ctrl_flag unembed_ctrl_flag t_ctrl_flag 
let (e_ctrl_flag_nbe :
  FStar_Tactics_Types.ctrl_flag FStar_TypeChecker_NBETerm.embedding) =
  let embed_ctrl_flag cb res =
    match res with
    | FStar_Tactics_Types.Continue  ->
        mkConstruct fstar_tactics_Continue_fv [] []
    | FStar_Tactics_Types.Skip  -> mkConstruct fstar_tactics_Skip_fv [] []
    | FStar_Tactics_Types.Abort  -> mkConstruct fstar_tactics_Abort_fv [] []
     in
  let unembed_ctrl_flag cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2405,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2421,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2437,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2452 ->
        ((let uu____2454 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____2454
          then
            let uu____2478 =
              let uu____2484 =
                let uu____2486 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2486
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2484)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2478
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____2492 = mkFV fv_ctrl_flag [] []  in
  let uu____2497 = fv_as_emb_typ fv_ctrl_flag  in
  {
    FStar_TypeChecker_NBETerm.em = embed_ctrl_flag;
    FStar_TypeChecker_NBETerm.un = unembed_ctrl_flag;
    FStar_TypeChecker_NBETerm.typ = uu____2492;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2497
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
    let uu____2529 =
      let uu____2530 = FStar_Syntax_Subst.compress t  in
      uu____2530.FStar_Syntax_Syntax.n  in
    match uu____2529 with
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
    | uu____2539 ->
        (if w
         then
           (let uu____2542 =
              let uu____2548 =
                let uu____2550 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____2550
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2548)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2542)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2604,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2620,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2636,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2652,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2667 -> FStar_Pervasives_Native.None  in
  let uu____2668 = mkFV fv_guard_policy [] []  in
  let uu____2673 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____2668;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2673
  } 