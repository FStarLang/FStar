open Prims
type name = FStar_Syntax_Syntax.bv
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  -> FStar_Parser_Const.fstar_tactics_lid' s 
let (lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____20 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____20 FStar_Syntax_Syntax.fv_to_tm
  
let (mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____29 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____29
  
type tac_constant =
  {
  lid: FStar_Ident.lid ;
  fv: FStar_Syntax_Syntax.fv ;
  t: FStar_Syntax_Syntax.term }
let (__proj__Mktac_constant__item__lid : tac_constant -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | { lid; fv; t;_} -> lid 
let (__proj__Mktac_constant__item__fv :
  tac_constant -> FStar_Syntax_Syntax.fv) =
  fun projectee  -> match projectee with | { lid; fv; t;_} -> fv 
let (__proj__Mktac_constant__item__t :
  tac_constant -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | { lid; fv; t;_} -> t 
let (lid_as_data_fv : FStar_Ident.lident -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    let uu____88 = lid_as_data_fv l  in FStar_Syntax_Syntax.fv_to_tm uu____88
  
let (fstar_tactics_data : Prims.string Prims.list -> tac_constant) =
  fun ns  ->
    let lid = fstar_tactics_lid' ns  in
    let uu____102 = lid_as_data_fv lid  in
    let uu____103 = lid_as_data_tm lid  in
    { lid; fv = uu____102; t = uu____103 }
  
let (fstar_tactics_const : Prims.string Prims.list -> tac_constant) =
  fun ns  ->
    let lid = fstar_tactics_lid' ns  in
    let uu____117 = FStar_Syntax_Syntax.fvconst lid  in
    let uu____118 = FStar_Syntax_Syntax.tconst lid  in
    { lid; fv = uu____117; t = uu____118 }
  
let (fstar_tactics_proofstate : tac_constant) =
  fstar_tactics_const ["Types"; "proofstate"] 
let (fstar_tactics_goal : tac_constant) =
  fstar_tactics_const ["Types"; "goal"] 
let (fstar_tactics_TacticFailure : tac_constant) =
  fstar_tactics_data ["Types"; "TacticFailure"] 
let (fstar_tactics_result : tac_constant) =
  fstar_tactics_const ["Types"; "result"] 
let (fstar_tactics_Success : tac_constant) =
  fstar_tactics_data ["Result"; "Success"] 
let (fstar_tactics_Failed : tac_constant) =
  fstar_tactics_data ["Result"; "Failed"] 
let (fstar_tactics_direction : tac_constant) =
  fstar_tactics_const ["Types"; "direction"] 
let (fstar_tactics_topdown : tac_constant) =
  fstar_tactics_data ["Types"; "TopDown"] 
let (fstar_tactics_bottomup : tac_constant) =
  fstar_tactics_data ["Types"; "BottomUp"] 
let (fstar_tactics_ctrl_flag : tac_constant) =
  fstar_tactics_const ["Types"; "ctrl_flag"] 
let (fstar_tactics_Continue : tac_constant) =
  fstar_tactics_data ["Types"; "Continue"] 
let (fstar_tactics_Skip : tac_constant) =
  fstar_tactics_data ["Types"; "Skip"] 
let (fstar_tactics_Abort : tac_constant) =
  fstar_tactics_data ["Types"; "Abort"] 
let (fstar_tactics_guard_policy : tac_constant) =
  fstar_tactics_const ["Types"; "guard_policy"] 
let (fstar_tactics_SMT : tac_constant) = fstar_tactics_data ["Types"; "SMT"] 
let (fstar_tactics_Goal : tac_constant) =
  fstar_tactics_data ["Types"; "Goal"] 
let (fstar_tactics_Drop : tac_constant) =
  fstar_tactics_data ["Types"; "Drop"] 
let (fstar_tactics_Force : tac_constant) =
  fstar_tactics_data ["Types"; "Force"] 
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
        let uu____280 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____280
  
let embed :
  'uuuuuu307 .
    'uuuuuu307 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'uuuuuu307 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____327 = FStar_Syntax_Embeddings.embed e x  in
        uu____327 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'uuuuuu345 .
    Prims.bool ->
      'uuuuuu345 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term -> 'uuuuuu345 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____369 = FStar_Syntax_Embeddings.unembed e x  in
        uu____369 w FStar_Syntax_Embeddings.id_norm_cb
  
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____384 =
      let uu____395 = FStar_Syntax_Syntax.as_arg t  in [uu____395]  in
    FStar_Syntax_Util.mk_app fstar_tactics_result.t uu____384
  
let (hd'_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun tm  ->
    let tm1 = FStar_Syntax_Util.unascribe tm  in
    let uu____441 = FStar_Syntax_Util.head_and_args tm1  in
    match uu____441 with
    | (hd,args) ->
        let uu____498 =
          let uu____499 = FStar_Syntax_Util.un_uinst hd  in
          uu____499.FStar_Syntax_Syntax.n  in
        (uu____498, args)
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps fstar_tactics_proofstate.t
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____543 =
      let uu____544 = FStar_Syntax_Subst.compress t  in
      uu____544.FStar_Syntax_Syntax.n  in
    match uu____543 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____550;
          FStar_Syntax_Syntax.rng = uu____551;_}
        ->
        let uu____554 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun uu____557  -> FStar_Pervasives_Native.Some uu____557)
          uu____554
    | uu____558 ->
        (if w
         then
           (let uu____561 =
              let uu____567 =
                let uu____569 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s\n"
                  uu____569
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____567)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____561)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_proofstate unembed_proofstate fstar_tactics_proofstate.t 
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
    let uu____660 =
      let uu____668 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____668, [])  in
    FStar_Syntax_Syntax.ET_app uu____660
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____688 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____688;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = (fstar_tactics_proofstate.t);
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk =
      FStar_Thunk.mk
        (fun uu____693  ->
           FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
             (FStar_TypeChecker_NBETerm.Constant
                (FStar_TypeChecker_NBETerm.String
                   ("(((proofstate.nbe)))", FStar_Range.dummyRange))))
       in
    FStar_TypeChecker_NBETerm.mk_t
      (FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk))
     in
  let unembed_proofstate _cb t =
    let uu____725 = FStar_TypeChecker_NBETerm.nbe_t_of_t t  in
    match uu____725 with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
           FStar_Syntax_Syntax.ltyp = uu____729;
           FStar_Syntax_Syntax.rng = uu____730;_},uu____731)
        ->
        let uu____750 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun uu____753  -> FStar_Pervasives_Native.Some uu____753)
          uu____750
    | uu____754 ->
        ((let uu____756 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____756
          then
            let uu____780 =
              let uu____786 =
                let uu____788 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded NBE proofstate: %s\n"
                  uu____788
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____786)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____780
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____794 = mkFV fstar_tactics_proofstate.fv [] []  in
  let uu____799 = fv_as_emb_typ fstar_tactics_proofstate.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____794;
    FStar_TypeChecker_NBETerm.emb_typ = uu____799
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g fstar_tactics_goal.t
      FStar_Syntax_Syntax.Lazy_goal (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____831 =
      let uu____832 = FStar_Syntax_Subst.compress t  in
      uu____832.FStar_Syntax_Syntax.n  in
    match uu____831 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____838;
          FStar_Syntax_Syntax.rng = uu____839;_}
        ->
        let uu____842 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun uu____845  -> FStar_Pervasives_Native.Some uu____845)
          uu____842
    | uu____846 ->
        (if w
         then
           (let uu____849 =
              let uu____855 =
                let uu____857 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____857  in
              (FStar_Errors.Warning_NotEmbedded, uu____855)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____849)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_goal unembed_goal fstar_tactics_goal.t 
let (unfold_lazy_goal :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((goal)))" 
let (e_goal_nbe :
  FStar_Tactics_Types.goal FStar_TypeChecker_NBETerm.embedding) =
  let embed_goal _cb ps =
    let li =
      let uu____885 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____885;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = (fstar_tactics_goal.t);
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk =
      FStar_Thunk.mk
        (fun uu____890  ->
           FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
             (FStar_TypeChecker_NBETerm.Constant
                (FStar_TypeChecker_NBETerm.String
                   ("(((goal.nbe)))", FStar_Range.dummyRange))))
       in
    FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
      (FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk))
     in
  let unembed_goal _cb t =
    let uu____922 = FStar_TypeChecker_NBETerm.nbe_t_of_t t  in
    match uu____922 with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
           FStar_Syntax_Syntax.ltyp = uu____926;
           FStar_Syntax_Syntax.rng = uu____927;_},uu____928)
        ->
        let uu____947 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun uu____950  -> FStar_Pervasives_Native.Some uu____950)
          uu____947
    | uu____951 ->
        ((let uu____953 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____953
          then
            let uu____977 =
              let uu____983 =
                let uu____985 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded NBE goal: %s" uu____985
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____983)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____977
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____991 = mkFV fstar_tactics_goal.fv [] []  in
  let uu____996 = fv_as_emb_typ fstar_tactics_goal.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____991;
    FStar_TypeChecker_NBETerm.emb_typ = uu____996
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____1022 uu____1023 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1027 =
          let uu____1028 =
            let uu____1037 = embed FStar_Syntax_Embeddings.e_string rng s  in
            FStar_Syntax_Syntax.as_arg uu____1037  in
          [uu____1028]  in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t
          uu____1027 rng
    | FStar_Tactics_Types.EExn t ->
        let uu___131_1056 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___131_1056.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___131_1056.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____1060 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____1060  in
        let uu____1063 =
          let uu____1064 =
            let uu____1073 = embed FStar_Syntax_Embeddings.e_string rng s  in
            FStar_Syntax_Syntax.as_arg uu____1073  in
          [uu____1064]  in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t
          uu____1063 rng
     in
  let unembed_exn t w uu____1110 =
    let uu____1115 = hd'_and_args t  in
    match uu____1115 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1134)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
        let uu____1169 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____1169
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1178 -> FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____1193 =
    let uu____1194 =
      let uu____1202 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____1202, [])  in
    FStar_Syntax_Syntax.ET_app uu____1194  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____1209  -> "(exn)") uu____1193
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1227 =
          let uu____1234 =
            let uu____1239 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____1239  in
          [uu____1234]  in
        mkConstruct fstar_tactics_TacticFailure.fv [] uu____1227
    | uu____1249 ->
        let uu____1250 =
          let uu____1252 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____1252  in
        failwith uu____1250
     in
  let unembed_exn cb t =
    let uu____1270 = FStar_TypeChecker_NBETerm.nbe_t_of_t t  in
    match uu____1270 with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1274,(s,uu____1276)::[])
        when FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid
        ->
        let uu____1295 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1295
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1304 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____1306 = mkFV fv_exn [] []  in
  let uu____1311 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____1306;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1311
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____1353 uu____1354 =
      match res with
      | FStar_Tactics_Result.Success (a1,ps) ->
          let uu____1360 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success.t
              [FStar_Syntax_Syntax.U_zero]
             in
          let uu____1361 =
            let uu____1362 =
              let uu____1371 = FStar_Syntax_Embeddings.type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1371  in
            let uu____1372 =
              let uu____1383 =
                let uu____1392 = embed ea rng a1  in
                FStar_Syntax_Syntax.as_arg uu____1392  in
              let uu____1393 =
                let uu____1404 =
                  let uu____1413 = embed e_proofstate rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1413  in
                [uu____1404]  in
              uu____1383 :: uu____1393  in
            uu____1362 :: uu____1372  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1360 uu____1361 rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1448 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed.t
              [FStar_Syntax_Syntax.U_zero]
             in
          let uu____1449 =
            let uu____1450 =
              let uu____1459 = FStar_Syntax_Embeddings.type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1459  in
            let uu____1460 =
              let uu____1471 =
                let uu____1480 = embed e_exn rng e  in
                FStar_Syntax_Syntax.as_arg uu____1480  in
              let uu____1481 =
                let uu____1492 =
                  let uu____1501 = embed e_proofstate rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1501  in
                [uu____1492]  in
              uu____1471 :: uu____1481  in
            uu____1450 :: uu____1460  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1448 uu____1449 rng
       in
    let unembed_result t w uu____1555 =
      let uu____1562 = hd'_and_args t  in
      match uu____1562 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a1,uu____1584)::(ps,uu____1586)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu____1653 = unembed' w ea a1  in
          FStar_Util.bind_opt uu____1653
            (fun a2  ->
               let uu____1661 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1661
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a2, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____1673)::(ps,uu____1675)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu____1742 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____1742
            (fun e1  ->
               let uu____1750 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1750
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1759 ->
          (if w
           then
             (let uu____1776 =
                let uu____1782 =
                  let uu____1784 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1784
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____1782)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1776)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____1792 =
      let uu____1793 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____1793  in
    let uu____1794 =
      let uu____1795 =
        let uu____1803 =
          FStar_All.pipe_right fstar_tactics_result.lid
            FStar_Ident.string_of_lid
           in
        let uu____1806 =
          let uu____1809 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____1809]  in
        (uu____1803, uu____1806)  in
      FStar_Syntax_Syntax.ET_app uu____1795  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1792 (fun uu____1816  -> "") uu____1794
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1856 =
            let uu____1863 =
              let uu____1868 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1868  in
            let uu____1869 =
              let uu____1876 =
                let uu____1881 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____1881  in
              let uu____1882 =
                let uu____1889 =
                  let uu____1894 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1894  in
                [uu____1889]  in
              uu____1876 :: uu____1882  in
            uu____1863 :: uu____1869  in
          mkConstruct fstar_tactics_Failed.fv [FStar_Syntax_Syntax.U_zero]
            uu____1856
      | FStar_Tactics_Result.Success (a1,ps) ->
          let uu____1913 =
            let uu____1920 =
              let uu____1925 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1925  in
            let uu____1926 =
              let uu____1933 =
                let uu____1938 = FStar_TypeChecker_NBETerm.embed ea cb a1  in
                FStar_TypeChecker_NBETerm.as_arg uu____1938  in
              let uu____1939 =
                let uu____1946 =
                  let uu____1951 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1951  in
                [uu____1946]  in
              uu____1933 :: uu____1939  in
            uu____1920 :: uu____1926  in
          mkConstruct fstar_tactics_Success.fv [FStar_Syntax_Syntax.U_zero]
            uu____1913
       in
    let unembed_result cb t =
      let uu____1987 = FStar_TypeChecker_NBETerm.nbe_t_of_t t  in
      match uu____1987 with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1993,(ps,uu____1995)::(a1,uu____1997)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu____2029 = FStar_TypeChecker_NBETerm.unembed ea cb a1  in
          FStar_Util.bind_opt uu____2029
            (fun a2  ->
               let uu____2037 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____2037
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a2, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2047,(ps,uu____2049)::(e,uu____2051)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu____2083 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____2083
            (fun e1  ->
               let uu____2091 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____2091
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____2100 -> FStar_Pervasives_Native.None  in
    let uu____2103 = mkFV fstar_tactics_result.fv [] []  in
    let uu____2108 = fv_as_emb_typ fstar_tactics_result.fv  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____2103;
      FStar_TypeChecker_NBETerm.emb_typ = uu____2108
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown.t
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup.t  in
  let unembed_direction w t =
    let uu____2142 =
      let uu____2143 = FStar_Syntax_Subst.compress t  in
      uu____2143.FStar_Syntax_Syntax.n  in
    match uu____2142 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2150 ->
        (if w
         then
           (let uu____2153 =
              let uu____2159 =
                let uu____2161 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2161
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2159)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2153)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_direction unembed_direction fstar_tactics_direction.t 
let (e_direction_nbe :
  FStar_Tactics_Types.direction FStar_TypeChecker_NBETerm.embedding) =
  let embed_direction cb res =
    match res with
    | FStar_Tactics_Types.TopDown  ->
        mkConstruct fstar_tactics_topdown.fv [] []
    | FStar_Tactics_Types.BottomUp  ->
        mkConstruct fstar_tactics_bottomup.fv [] []
     in
  let unembed_direction cb t =
    let uu____2204 = FStar_TypeChecker_NBETerm.nbe_t_of_t t  in
    match uu____2204 with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2208,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2224,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2239 ->
        ((let uu____2241 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____2241
          then
            let uu____2265 =
              let uu____2271 =
                let uu____2273 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2273
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2271)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2265
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____2279 = mkFV fstar_tactics_direction.fv [] []  in
  let uu____2284 = fv_as_emb_typ fstar_tactics_direction.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____2279;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2284
  } 
let (e_ctrl_flag :
  FStar_Tactics_Types.ctrl_flag FStar_Syntax_Embeddings.embedding) =
  let embed_ctrl_flag rng d =
    match d with
    | FStar_Tactics_Types.Continue  -> fstar_tactics_Continue.t
    | FStar_Tactics_Types.Skip  -> fstar_tactics_Skip.t
    | FStar_Tactics_Types.Abort  -> fstar_tactics_Abort.t  in
  let unembed_ctrl_flag w t =
    let uu____2316 =
      let uu____2317 = FStar_Syntax_Subst.compress t  in
      uu____2317.FStar_Syntax_Syntax.n  in
    match uu____2316 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2325 ->
        (if w
         then
           (let uu____2328 =
              let uu____2334 =
                let uu____2336 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2336
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2334)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2328)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_ctrl_flag unembed_ctrl_flag fstar_tactics_ctrl_flag.t 
let (e_ctrl_flag_nbe :
  FStar_Tactics_Types.ctrl_flag FStar_TypeChecker_NBETerm.embedding) =
  let embed_ctrl_flag cb res =
    match res with
    | FStar_Tactics_Types.Continue  ->
        mkConstruct fstar_tactics_Continue.fv [] []
    | FStar_Tactics_Types.Skip  -> mkConstruct fstar_tactics_Skip.fv [] []
    | FStar_Tactics_Types.Abort  -> mkConstruct fstar_tactics_Abort.fv [] []
     in
  let unembed_ctrl_flag cb t =
    let uu____2383 = FStar_TypeChecker_NBETerm.nbe_t_of_t t  in
    match uu____2383 with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2387,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2403,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2419,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2434 ->
        ((let uu____2436 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____2436
          then
            let uu____2460 =
              let uu____2466 =
                let uu____2468 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2468
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2466)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2460
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____2474 = mkFV fstar_tactics_ctrl_flag.fv [] []  in
  let uu____2479 = fv_as_emb_typ fstar_tactics_ctrl_flag.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_ctrl_flag;
    FStar_TypeChecker_NBETerm.un = unembed_ctrl_flag;
    FStar_TypeChecker_NBETerm.typ = uu____2474;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2479
  } 
let (e_guard_policy :
  FStar_Tactics_Types.guard_policy FStar_Syntax_Embeddings.embedding) =
  let embed_guard_policy rng p =
    match p with
    | FStar_Tactics_Types.SMT  -> fstar_tactics_SMT.t
    | FStar_Tactics_Types.Goal  -> fstar_tactics_Goal.t
    | FStar_Tactics_Types.Force  -> fstar_tactics_Force.t
    | FStar_Tactics_Types.Drop  -> fstar_tactics_Drop.t  in
  let unembed_guard_policy w t =
    let uu____2511 =
      let uu____2512 = FStar_Syntax_Subst.compress t  in
      uu____2512.FStar_Syntax_Syntax.n  in
    match uu____2511 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2521 ->
        (if w
         then
           (let uu____2524 =
              let uu____2530 =
                let uu____2532 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____2532
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2530)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2524)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_guard_policy unembed_guard_policy fstar_tactics_guard_policy.t 
let (e_guard_policy_nbe :
  FStar_Tactics_Types.guard_policy FStar_TypeChecker_NBETerm.embedding) =
  let embed_guard_policy cb p =
    match p with
    | FStar_Tactics_Types.SMT  -> mkConstruct fstar_tactics_SMT.fv [] []
    | FStar_Tactics_Types.Goal  -> mkConstruct fstar_tactics_Goal.fv [] []
    | FStar_Tactics_Types.Force  -> mkConstruct fstar_tactics_Force.fv [] []
    | FStar_Tactics_Types.Drop  -> mkConstruct fstar_tactics_Drop.fv [] []
     in
  let unembed_guard_policy cb t =
    let uu____2583 = FStar_TypeChecker_NBETerm.nbe_t_of_t t  in
    match uu____2583 with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2587,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2603,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2619,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2635,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2650 -> FStar_Pervasives_Native.None  in
  let uu____2651 = mkFV fstar_tactics_guard_policy.fv [] []  in
  let uu____2656 = fv_as_emb_typ fstar_tactics_guard_policy.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____2651;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2656
  } 