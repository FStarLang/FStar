open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____38 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____38 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____64 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____64
  
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____112 = lid_as_data_fv l  in
    FStar_Syntax_Syntax.fv_to_tm uu____112
  
let (fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    let uu____131 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____131
  
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
  let uu____453 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____453 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____474 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____474 
let (t_goal : FStar_Syntax_Syntax.term) =
  let uu____497 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.tconst uu____497 
let (fv_goal : FStar_Syntax_Syntax.fv) =
  let uu____518 = fstar_tactics_lid' ["Types"; "goal"]  in
  FStar_Syntax_Syntax.fvconst uu____518 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____562 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____562 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____596 =
      let uu____611 = FStar_Syntax_Syntax.as_arg t  in [uu____611]  in
    FStar_Syntax_Util.mk_app t_result uu____596
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____657 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____657 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____678 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____678 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____701 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____701 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____722 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____722 
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
        let uu____813 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____813
  
let embed :
  'Auu____850 .
    'Auu____850 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____850 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____874 = FStar_Syntax_Embeddings.embed e x  in
        uu____874 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____896 .
    Prims.bool ->
      'Auu____896 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____896 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____928 = FStar_Syntax_Embeddings.unembed e x  in
        uu____928 w FStar_Syntax_Embeddings.id_norm_cb
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____976 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____976 with
    | (hd1,args) ->
        let uu____1061 =
          let uu____1062 = FStar_Syntax_Util.un_uinst hd1  in
          uu____1062.FStar_Syntax_Syntax.n  in
        (uu____1061, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____1536 =
      let uu____1537 = FStar_Syntax_Subst.compress t  in
      uu____1537.FStar_Syntax_Syntax.n  in
    match uu____1536 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____1618;
          FStar_Syntax_Syntax.rng = uu____1619;_}
        ->
        let uu____1626 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _2031  -> FStar_Pervasives_Native.Some _2031) uu____1626
    | uu____2032 ->
        (if w
         then
           (let uu____2035 =
              let uu____2041 =
                let uu____2043 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s"
                  uu____2043
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2041)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2035)
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
    let uu____2302 =
      let uu____2310 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____2310, [])  in
    FStar_Syntax_Syntax.ET_app uu____2302
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____2558 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____2558;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____2630  ->
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
           FStar_Syntax_Syntax.ltyp = uu____2813;
           FStar_Syntax_Syntax.rng = uu____2814;_},uu____2815)
        ->
        let uu____2846 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _3251  -> FStar_Pervasives_Native.Some _3251) uu____2846
    | uu____3252 ->
        ((let uu____3254 =
            let uu____3260 =
              let uu____3262 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____3262
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3260)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3254);
         FStar_Pervasives_Native.None)
     in
  let uu____3333 = mkFV fv_proofstate [] []  in
  let uu____3338 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____3333;
    FStar_TypeChecker_NBETerm.emb_typ = uu____3338
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____3807 =
      let uu____3808 = FStar_Syntax_Subst.compress t  in
      uu____3808.FStar_Syntax_Syntax.n  in
    match uu____3807 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____3881;
          FStar_Syntax_Syntax.rng = uu____3882;_}
        ->
        let uu____3889 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _4246  -> FStar_Pervasives_Native.Some _4246) uu____3889
    | uu____4247 ->
        (if w
         then
           (let uu____4250 =
              let uu____4256 =
                let uu____4258 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____4258  in
              (FStar_Errors.Warning_NotEmbedded, uu____4256)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4250)
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
      let uu____4620 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____4620;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk1 =
      FStar_Common.mk_thunk
        (fun uu____4684  ->
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
           FStar_Syntax_Syntax.ltyp = uu____4851;
           FStar_Syntax_Syntax.rng = uu____4852;_},uu____4853)
        ->
        let uu____4884 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _5241  -> FStar_Pervasives_Native.Some _5241) uu____4884
    | uu____5242 ->
        ((let uu____5244 =
            let uu____5250 =
              let uu____5252 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE goal: %s" uu____5252
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5250)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5244);
         FStar_Pervasives_Native.None)
     in
  let uu____5315 = mkFV fv_goal [] []  in
  let uu____5320 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____5315;
    FStar_TypeChecker_NBETerm.emb_typ = uu____5320
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____5409 uu____5410 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____5418 =
          let uu____5423 =
            let uu____5424 =
              let uu____5437 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____5437  in
            [uu____5424]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____5423
           in
        uu____5418 FStar_Pervasives_Native.None rng
    | FStar_Tactics_Types.EExn t ->
        let uu___117_5476 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___117_5476.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___117_5476.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____5488 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____5488  in
        let uu____5491 =
          let uu____5496 =
            let uu____5497 =
              let uu____5510 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____5510  in
            [uu____5497]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure_tm
            uu____5496
           in
        uu____5491 FStar_Pervasives_Native.None rng
     in
  let unembed_exn t w uu____5567 =
    let uu____5576 = hd'_and_args t  in
    match uu____5576 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____5599)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid ->
        let uu____5657 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____5657
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____5666 -> FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____5685 =
    let uu____5686 =
      let uu____5694 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____5694, [])  in
    FStar_Syntax_Syntax.ET_app uu____5686  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____5705  -> "(exn)") uu____5685
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____5738 =
          let uu____5745 =
            let uu____5750 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____5750  in
          [uu____5745]  in
        mkConstruct fstar_tactics_TacticFailure_fv [] uu____5738
    | uu____5760 ->
        let uu____5761 =
          let uu____5763 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____5763  in
        failwith uu____5761
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____5790,(s,uu____5792)::[])
        when FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure_lid
        ->
        let uu____5817 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____5817
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____5826 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____5834 = mkFV fv_exn [] []  in
  let uu____5839 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____5834;
    FStar_TypeChecker_NBETerm.emb_typ = uu____5839
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____5885 uu____5886 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____6030 =
            let uu____6035 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____6044 =
              let uu____6045 =
                let uu____6058 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____6058  in
              let uu____6067 =
                let uu____6082 =
                  let uu____6095 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____6095  in
                let uu____6104 =
                  let uu____6119 =
                    let uu____6132 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____6132  in
                  [uu____6119]  in
                uu____6082 :: uu____6104  in
              uu____6045 :: uu____6067  in
            FStar_Syntax_Syntax.mk_Tm_app uu____6035 uu____6044  in
          uu____6030 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____6392 =
            let uu____6397 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____6406 =
              let uu____6407 =
                let uu____6420 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____6420  in
              let uu____6429 =
                let uu____6444 =
                  let uu____6457 = embed e_exn rng e  in
                  FStar_Syntax_Syntax.as_arg uu____6457  in
                let uu____6466 =
                  let uu____6481 =
                    let uu____6494 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____6494  in
                  [uu____6481]  in
                uu____6444 :: uu____6466  in
              uu____6407 :: uu____6429  in
            FStar_Syntax_Syntax.mk_Tm_app uu____6397 uu____6406  in
          uu____6392 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____6643 =
      let uu____6654 = hd'_and_args t  in
      match uu____6654 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____6680)::(ps,uu____6682)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____6792 = unembed' w ea a  in
          FStar_Util.bind_opt uu____6792
            (fun a1  ->
               let uu____6800 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____6800
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____7147)::(ps,uu____7149)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____7259 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____7259
            (fun e1  ->
               let uu____7267 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____7267
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____7611 ->
          (if w
           then
             (let uu____7632 =
                let uu____7638 =
                  let uu____7640 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____7640
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____7638)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____7632)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____7648 =
      let uu____7657 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____7657  in
    let uu____7666 =
      let uu____7667 =
        let uu____7675 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____7682 =
          let uu____7685 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____7685]  in
        (uu____7675, uu____7682)  in
      FStar_Syntax_Syntax.ET_app uu____7667  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____7648 (fun uu____7692  -> "") uu____7666
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____7888 =
            let uu____7895 =
              let uu____7900 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____7900  in
            let uu____7901 =
              let uu____7908 =
                let uu____7913 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____7913  in
              let uu____7914 =
                let uu____7921 =
                  let uu____7926 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____7926  in
                [uu____7921]  in
              uu____7908 :: uu____7914  in
            uu____7895 :: uu____7901  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____7888
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____8146 =
            let uu____8153 =
              let uu____8158 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____8158  in
            let uu____8159 =
              let uu____8166 =
                let uu____8171 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____8171  in
              let uu____8172 =
                let uu____8179 =
                  let uu____8184 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____8184  in
                [uu____8179]  in
              uu____8166 :: uu____8172  in
            uu____8153 :: uu____8159  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____8146
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____8296,(ps,uu____8298)::(a,uu____8300)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____8338 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____8338
            (fun a1  ->
               let uu____8346 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____8346
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____8691,(ps,uu____8693)::(e,uu____8695)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____8733 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____8733
            (fun e1  ->
               let uu____8741 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____8741
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____9085 -> FStar_Pervasives_Native.None  in
    let uu____9088 = mkFV fv_result [] []  in
    let uu____9093 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____9088;
      FStar_TypeChecker_NBETerm.emb_typ = uu____9093
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____9147 =
      let uu____9148 = FStar_Syntax_Subst.compress t  in
      uu____9148.FStar_Syntax_Syntax.n  in
    match uu____9147 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____9169 ->
        (if w
         then
           (let uu____9172 =
              let uu____9178 =
                let uu____9180 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____9180
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____9178)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____9172)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____9247,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____9269,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____9290 ->
        ((let uu____9292 =
            let uu____9298 =
              let uu____9300 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____9300
               in
            (FStar_Errors.Warning_NotEmbedded, uu____9298)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____9292);
         FStar_Pervasives_Native.None)
     in
  let uu____9304 = mkFV fv_direction [] []  in
  let uu____9309 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____9304;
    FStar_TypeChecker_NBETerm.emb_typ = uu____9309
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
    let uu____9361 =
      let uu____9362 = FStar_Syntax_Subst.compress t  in
      uu____9362.FStar_Syntax_Syntax.n  in
    match uu____9361 with
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
    | uu____9391 ->
        (if w
         then
           (let uu____9394 =
              let uu____9400 =
                let uu____9402 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____9402
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____9400)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____9394)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____9479,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____9501,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____9523,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____9545,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____9566 -> FStar_Pervasives_Native.None  in
  let uu____9567 = mkFV fv_guard_policy [] []  in
  let uu____9572 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____9567;
    FStar_TypeChecker_NBETerm.emb_typ = uu____9572
  } 