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
           FStar_Syntax_Syntax.ltyp = uu____726;
           FStar_Syntax_Syntax.rng = uu____727;_},uu____728)
        ->
        let uu____747 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun uu____750  -> FStar_Pervasives_Native.Some uu____750)
          uu____747
    | uu____751 ->
        ((let uu____753 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____753
          then
            let uu____777 =
              let uu____783 =
                let uu____785 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded NBE proofstate: %s\n"
                  uu____785
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____783)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____777
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____791 = mkFV fstar_tactics_proofstate.fv [] []  in
  let uu____796 = fv_as_emb_typ fstar_tactics_proofstate.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____791;
    FStar_TypeChecker_NBETerm.emb_typ = uu____796
  } 
let (e_goal : FStar_Tactics_Types.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g fstar_tactics_goal.t
      FStar_Syntax_Syntax.Lazy_goal (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____828 =
      let uu____829 = FStar_Syntax_Subst.compress t  in
      uu____829.FStar_Syntax_Syntax.n  in
    match uu____828 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____835;
          FStar_Syntax_Syntax.rng = uu____836;_}
        ->
        let uu____839 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun uu____842  -> FStar_Pervasives_Native.Some uu____842)
          uu____839
    | uu____843 ->
        (if w
         then
           (let uu____846 =
              let uu____852 =
                let uu____854 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____854  in
              (FStar_Errors.Warning_NotEmbedded, uu____852)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____846)
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
      let uu____882 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____882;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = (fstar_tactics_goal.t);
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    let thunk =
      FStar_Thunk.mk
        (fun uu____887  ->
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
           FStar_Syntax_Syntax.ltyp = uu____920;
           FStar_Syntax_Syntax.rng = uu____921;_},uu____922)
        ->
        let uu____941 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun uu____944  -> FStar_Pervasives_Native.Some uu____944)
          uu____941
    | uu____945 ->
        ((let uu____947 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____947
          then
            let uu____971 =
              let uu____977 =
                let uu____979 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded NBE goal: %s" uu____979
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____977)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____971
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____985 = mkFV fstar_tactics_goal.fv [] []  in
  let uu____990 = fv_as_emb_typ fstar_tactics_goal.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____985;
    FStar_TypeChecker_NBETerm.emb_typ = uu____990
  } 
let (e_exn : Prims.exn FStar_Syntax_Embeddings.embedding) =
  let embed_exn e rng uu____1016 uu____1017 =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1021 =
          let uu____1022 =
            let uu____1031 = embed FStar_Syntax_Embeddings.e_string rng s  in
            FStar_Syntax_Syntax.as_arg uu____1031  in
          [uu____1022]  in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t
          uu____1021 rng
    | FStar_Tactics_Types.EExn t ->
        let uu___131_1050 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___131_1050.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___131_1050.FStar_Syntax_Syntax.vars)
        }
    | e1 ->
        let s =
          let uu____1054 = FStar_Util.message_of_exn e1  in
          Prims.op_Hat "uncaught exception: " uu____1054  in
        let uu____1057 =
          let uu____1058 =
            let uu____1067 = embed FStar_Syntax_Embeddings.e_string rng s  in
            FStar_Syntax_Syntax.as_arg uu____1067  in
          [uu____1058]  in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_TacticFailure.t
          uu____1057 rng
     in
  let unembed_exn t w uu____1104 =
    let uu____1109 = hd'_and_args t  in
    match uu____1109 with
    | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1128)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
        let uu____1163 = unembed' w FStar_Syntax_Embeddings.e_string s  in
        FStar_Util.bind_opt uu____1163
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1172 -> FStar_Pervasives_Native.Some (FStar_Tactics_Types.EExn t)
     in
  let uu____1187 =
    let uu____1188 =
      let uu____1196 =
        FStar_All.pipe_right FStar_Parser_Const.exn_lid
          FStar_Ident.string_of_lid
         in
      (uu____1196, [])  in
    FStar_Syntax_Syntax.ET_app uu____1188  in
  FStar_Syntax_Embeddings.mk_emb_full embed_exn unembed_exn
    FStar_Syntax_Syntax.t_exn (fun uu____1203  -> "(exn)") uu____1187
  
let (e_exn_nbe : Prims.exn FStar_TypeChecker_NBETerm.embedding) =
  let embed_exn cb e =
    match e with
    | FStar_Tactics_Types.TacticFailure s ->
        let uu____1221 =
          let uu____1228 =
            let uu____1233 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____1233  in
          [uu____1228]  in
        mkConstruct fstar_tactics_TacticFailure.fv [] uu____1221
    | uu____1243 ->
        let uu____1244 =
          let uu____1246 = FStar_Util.message_of_exn e  in
          FStar_Util.format1 "cannot embed exn (NBE) : %s" uu____1246  in
        failwith uu____1244
     in
  let unembed_exn cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1265,(s,uu____1267)::[])
        when FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_TacticFailure.lid
        ->
        let uu____1286 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1286
          (fun s1  ->
             FStar_Pervasives_Native.Some
               (FStar_Tactics_Types.TacticFailure s1))
    | uu____1295 -> FStar_Pervasives_Native.None  in
  let fv_exn = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.exn_lid  in
  let uu____1297 = mkFV fv_exn [] []  in
  let uu____1302 = fv_as_emb_typ fv_exn  in
  {
    FStar_TypeChecker_NBETerm.em = embed_exn;
    FStar_TypeChecker_NBETerm.un = unembed_exn;
    FStar_TypeChecker_NBETerm.typ = uu____1297;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1302
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____1344 uu____1345 =
      match res with
      | FStar_Tactics_Result.Success (a1,ps) ->
          let uu____1351 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success.t
              [FStar_Syntax_Syntax.U_zero]
             in
          let uu____1352 =
            let uu____1353 =
              let uu____1362 = FStar_Syntax_Embeddings.type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1362  in
            let uu____1363 =
              let uu____1374 =
                let uu____1383 = embed ea rng a1  in
                FStar_Syntax_Syntax.as_arg uu____1383  in
              let uu____1384 =
                let uu____1395 =
                  let uu____1404 = embed e_proofstate rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1404  in
                [uu____1395]  in
              uu____1374 :: uu____1384  in
            uu____1353 :: uu____1363  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1351 uu____1352 rng
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1439 =
            FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed.t
              [FStar_Syntax_Syntax.U_zero]
             in
          let uu____1440 =
            let uu____1441 =
              let uu____1450 = FStar_Syntax_Embeddings.type_of ea  in
              FStar_Syntax_Syntax.iarg uu____1450  in
            let uu____1451 =
              let uu____1462 =
                let uu____1471 = embed e_exn rng e  in
                FStar_Syntax_Syntax.as_arg uu____1471  in
              let uu____1472 =
                let uu____1483 =
                  let uu____1492 = embed e_proofstate rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1492  in
                [uu____1483]  in
              uu____1462 :: uu____1472  in
            uu____1441 :: uu____1451  in
          FStar_Syntax_Syntax.mk_Tm_app uu____1439 uu____1440 rng
       in
    let unembed_result t w uu____1546 =
      let uu____1553 = hd'_and_args t  in
      match uu____1553 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a1,uu____1575)::(ps,uu____1577)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu____1644 = unembed' w ea a1  in
          FStar_Util.bind_opt uu____1644
            (fun a2  ->
               let uu____1652 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1652
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a2, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(e,uu____1664)::(ps,uu____1666)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu____1733 = unembed' w e_exn e  in
          FStar_Util.bind_opt uu____1733
            (fun e1  ->
               let uu____1741 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1741
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____1750 ->
          (if w
           then
             (let uu____1767 =
                let uu____1773 =
                  let uu____1775 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1775
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____1773)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1767)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____1783 =
      let uu____1784 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____1784  in
    let uu____1785 =
      let uu____1786 =
        let uu____1794 =
          FStar_All.pipe_right fstar_tactics_result.lid
            FStar_Ident.string_of_lid
           in
        let uu____1797 =
          let uu____1800 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____1800]  in
        (uu____1794, uu____1797)  in
      FStar_Syntax_Syntax.ET_app uu____1786  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1783 (fun uu____1807  -> "") uu____1785
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (e,ps) ->
          let uu____1847 =
            let uu____1854 =
              let uu____1859 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1859  in
            let uu____1860 =
              let uu____1867 =
                let uu____1872 =
                  FStar_TypeChecker_NBETerm.embed e_exn_nbe cb e  in
                FStar_TypeChecker_NBETerm.as_arg uu____1872  in
              let uu____1873 =
                let uu____1880 =
                  let uu____1885 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1885  in
                [uu____1880]  in
              uu____1867 :: uu____1873  in
            uu____1854 :: uu____1860  in
          mkConstruct fstar_tactics_Failed.fv [FStar_Syntax_Syntax.U_zero]
            uu____1847
      | FStar_Tactics_Result.Success (a1,ps) ->
          let uu____1904 =
            let uu____1911 =
              let uu____1916 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1916  in
            let uu____1917 =
              let uu____1924 =
                let uu____1929 = FStar_TypeChecker_NBETerm.embed ea cb a1  in
                FStar_TypeChecker_NBETerm.as_arg uu____1929  in
              let uu____1930 =
                let uu____1937 =
                  let uu____1942 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1942  in
                [uu____1937]  in
              uu____1924 :: uu____1930  in
            uu____1911 :: uu____1917  in
          mkConstruct fstar_tactics_Success.fv [FStar_Syntax_Syntax.U_zero]
            uu____1904
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1979,(ps,uu____1981)::(a1,uu____1983)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success.lid ->
          let uu____2015 = FStar_TypeChecker_NBETerm.unembed ea cb a1  in
          FStar_Util.bind_opt uu____2015
            (fun a2  ->
               let uu____2023 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____2023
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a2, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2033,(ps,uu____2035)::(e,uu____2037)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed.lid ->
          let uu____2069 = FStar_TypeChecker_NBETerm.unembed e_exn_nbe cb e
             in
          FStar_Util.bind_opt uu____2069
            (fun e1  ->
               let uu____2077 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____2077
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (e1, ps1))))
      | uu____2086 -> FStar_Pervasives_Native.None  in
    let uu____2089 = mkFV fstar_tactics_result.fv [] []  in
    let uu____2094 = fv_as_emb_typ fstar_tactics_result.fv  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____2089;
      FStar_TypeChecker_NBETerm.emb_typ = uu____2094
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown.t
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup.t  in
  let unembed_direction w t =
    let uu____2128 =
      let uu____2129 = FStar_Syntax_Subst.compress t  in
      uu____2129.FStar_Syntax_Syntax.n  in
    match uu____2128 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2136 ->
        (if w
         then
           (let uu____2139 =
              let uu____2145 =
                let uu____2147 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2147
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2145)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2139)
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
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2191,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2207,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____2222 ->
        ((let uu____2224 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____2224
          then
            let uu____2248 =
              let uu____2254 =
                let uu____2256 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____2256
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2254)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2248
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____2262 = mkFV fstar_tactics_direction.fv [] []  in
  let uu____2267 = fv_as_emb_typ fstar_tactics_direction.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____2262;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2267
  } 
let (e_ctrl_flag :
  FStar_Tactics_Types.ctrl_flag FStar_Syntax_Embeddings.embedding) =
  let embed_ctrl_flag rng d =
    match d with
    | FStar_Tactics_Types.Continue  -> fstar_tactics_Continue.t
    | FStar_Tactics_Types.Skip  -> fstar_tactics_Skip.t
    | FStar_Tactics_Types.Abort  -> fstar_tactics_Abort.t  in
  let unembed_ctrl_flag w t =
    let uu____2299 =
      let uu____2300 = FStar_Syntax_Subst.compress t  in
      uu____2300.FStar_Syntax_Syntax.n  in
    match uu____2299 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2308 ->
        (if w
         then
           (let uu____2311 =
              let uu____2317 =
                let uu____2319 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2319
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2317)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2311)
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
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2367,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Continue.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Continue
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2383,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Skip.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Skip
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2399,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Abort.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Abort
    | uu____2414 ->
        ((let uu____2416 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
          if uu____2416
          then
            let uu____2440 =
              let uu____2446 =
                let uu____2448 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded ctrl_flag: %s" uu____2448
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2446)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2440
          else ());
         FStar_Pervasives_Native.None)
     in
  let uu____2454 = mkFV fstar_tactics_ctrl_flag.fv [] []  in
  let uu____2459 = fv_as_emb_typ fstar_tactics_ctrl_flag.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_ctrl_flag;
    FStar_TypeChecker_NBETerm.un = unembed_ctrl_flag;
    FStar_TypeChecker_NBETerm.typ = uu____2454;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2459
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
    let uu____2491 =
      let uu____2492 = FStar_Syntax_Subst.compress t  in
      uu____2492.FStar_Syntax_Syntax.n  in
    match uu____2491 with
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
    | uu____2501 ->
        (if w
         then
           (let uu____2504 =
              let uu____2510 =
                let uu____2512 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____2512
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2510)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2504)
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
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2566,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2582,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2598,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2614,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop.lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____2629 -> FStar_Pervasives_Native.None  in
  let uu____2630 = mkFV fstar_tactics_guard_policy.fv [] []  in
  let uu____2635 = fv_as_emb_typ fstar_tactics_guard_policy.fv  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____2630;
    FStar_TypeChecker_NBETerm.emb_typ = uu____2635
  } 