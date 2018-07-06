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
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____308 =
      let uu____309 = FStar_Syntax_Subst.compress t  in
      uu____309.FStar_Syntax_Syntax.n  in
    match uu____308 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____315;
          FStar_Syntax_Syntax.rng = uu____316;_}
        ->
        let uu____319 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____319
    | uu____322 ->
        (if w
         then
           (let uu____324 =
              let uu____329 =
                let uu____330 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____330
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____329)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____324)
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
    let uu____412 =
      let uu____419 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____419, [])  in
    FStar_Syntax_Syntax.ET_app uu____412
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate _cb ps =
    let li =
      let uu____446 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____446;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li)  in
  let unembed_proofstate _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____481;
          FStar_Syntax_Syntax.rng = uu____482;_})
        ->
        let uu____493 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____493
    | uu____496 ->
        ((let uu____498 =
            let uu____503 =
              let uu____504 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____504
               in
            (FStar_Errors.Warning_NotEmbedded, uu____503)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____498);
         FStar_Pervasives_Native.None)
     in
  let uu____505 = mkFV fv_proofstate [] []  in
  let uu____510 = fv_as_emb_typ fv_proofstate  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____505;
    FStar_TypeChecker_NBETerm.emb_typ = uu____510
  } 
let (e_goal : FStar_Tactics_Basic.goal FStar_Syntax_Embeddings.embedding) =
  let embed_goal rng g =
    FStar_Syntax_Util.mk_lazy g t_goal FStar_Syntax_Syntax.Lazy_goal
      (FStar_Pervasives_Native.Some rng)
     in
  let unembed_goal w t =
    let uu____539 =
      let uu____540 = FStar_Syntax_Subst.compress t  in
      uu____540.FStar_Syntax_Syntax.n  in
    match uu____539 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____546;
          FStar_Syntax_Syntax.rng = uu____547;_}
        ->
        let uu____550 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_18  -> FStar_Pervasives_Native.Some _0_18) uu____550
    | uu____553 ->
        (if w
         then
           (let uu____555 =
              let uu____560 =
                let uu____561 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded goal: %s" uu____561  in
              (FStar_Errors.Warning_NotEmbedded, uu____560)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____555)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_goal unembed_goal t_goal 
let (unfold_lazy_goal :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_string "(((goal)))" 
let (e_goal_nbe :
  FStar_Tactics_Basic.goal FStar_TypeChecker_NBETerm.embedding) =
  let embed_goal _cb ps =
    let li =
      let uu____592 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____592;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal;
        FStar_Syntax_Syntax.ltyp = t_goal;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li)  in
  let unembed_goal _cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_goal ;
          FStar_Syntax_Syntax.ltyp = uu____627;
          FStar_Syntax_Syntax.rng = uu____628;_})
        ->
        let uu____639 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_19  -> FStar_Pervasives_Native.Some _0_19) uu____639
    | uu____642 ->
        ((let uu____644 =
            let uu____649 =
              let uu____650 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE goal: %s" uu____650  in
            (FStar_Errors.Warning_NotEmbedded, uu____649)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____644);
         FStar_Pervasives_Native.None)
     in
  let uu____651 = mkFV fv_goal [] []  in
  let uu____656 = fv_as_emb_typ fv_goal  in
  {
    FStar_TypeChecker_NBETerm.em = embed_goal;
    FStar_TypeChecker_NBETerm.un = unembed_goal;
    FStar_TypeChecker_NBETerm.typ = uu____651;
    FStar_TypeChecker_NBETerm.emb_typ = uu____656
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____717 uu____718 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____744 =
            let uu____749 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____750 =
              let uu____751 =
                let uu____760 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____760  in
              let uu____761 =
                let uu____772 =
                  let uu____781 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____781  in
                let uu____782 =
                  let uu____793 =
                    let uu____802 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____802  in
                  [uu____793]  in
                uu____772 :: uu____782  in
              uu____751 :: uu____761  in
            FStar_Syntax_Syntax.mk_Tm_app uu____749 uu____750  in
          uu____744 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (msg,ps) ->
          let uu____839 =
            let uu____844 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____845 =
              let uu____846 =
                let uu____855 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____855  in
              let uu____856 =
                let uu____867 =
                  let uu____876 =
                    embed FStar_Syntax_Embeddings.e_string rng msg  in
                  FStar_Syntax_Syntax.as_arg uu____876  in
                let uu____877 =
                  let uu____888 =
                    let uu____897 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____897  in
                  [uu____888]  in
                uu____867 :: uu____877  in
              uu____846 :: uu____856  in
            FStar_Syntax_Syntax.mk_Tm_app uu____844 uu____845  in
          uu____839 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____953 =
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____981 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____981 with
        | (hd1,args) ->
            let uu____1038 =
              let uu____1039 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1039.FStar_Syntax_Syntax.n  in
            (uu____1038, args)
         in
      let uu____1052 = hd'_and_args t  in
      match uu____1052 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____1074)::(ps,uu____1076)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1143 = unembed' w ea a  in
          FStar_Util.bind_opt uu____1143
            (fun a1  ->
               let uu____1151 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1151
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(msg,uu____1163)::(ps,uu____1165)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1232 = unembed' w FStar_Syntax_Embeddings.e_string msg
             in
          FStar_Util.bind_opt uu____1232
            (fun msg1  ->
               let uu____1240 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1240
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____1249 ->
          (if w
           then
             (let uu____1265 =
                let uu____1270 =
                  let uu____1271 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1271
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____1270)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1265)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____1275 =
      let uu____1276 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____1276  in
    let uu____1277 =
      let uu____1278 =
        let uu____1285 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____1286 =
          let uu____1289 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____1289]  in
        (uu____1285, uu____1286)  in
      FStar_Syntax_Syntax.ET_app uu____1278  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1275 (fun uu____1295  -> "") uu____1277
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result cb res =
      match res with
      | FStar_Tactics_Result.Failed (msg,ps) ->
          let uu____1343 =
            let uu____1350 =
              let uu____1355 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1355  in
            let uu____1356 =
              let uu____1363 =
                let uu____1368 =
                  FStar_TypeChecker_NBETerm.embed
                    FStar_TypeChecker_NBETerm.e_string cb msg
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1368  in
              let uu____1373 =
                let uu____1380 =
                  let uu____1385 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1385  in
                [uu____1380]  in
              uu____1363 :: uu____1373  in
            uu____1350 :: uu____1356  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____1343
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1408 =
            let uu____1415 =
              let uu____1420 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1420  in
            let uu____1421 =
              let uu____1428 =
                let uu____1433 = FStar_TypeChecker_NBETerm.embed ea cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1433  in
              let uu____1438 =
                let uu____1445 =
                  let uu____1450 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe cb ps
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____1450  in
                [uu____1445]  in
              uu____1428 :: uu____1438  in
            uu____1415 :: uu____1421  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____1408
       in
    let unembed_result cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1501,(ps,uu____1503)::(a,uu____1505)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1537 = FStar_TypeChecker_NBETerm.unembed ea cb a  in
          FStar_Util.bind_opt uu____1537
            (fun a1  ->
               let uu____1549 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____1549
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1563,(ps,uu____1565)::(msg,uu____1567)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1599 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_string cb msg
             in
          FStar_Util.bind_opt uu____1599
            (fun msg1  ->
               let uu____1611 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe cb ps  in
               FStar_Util.bind_opt uu____1611
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____1624 -> FStar_Pervasives_Native.None  in
    let uu____1627 = mkFV fv_result [] []  in
    let uu____1632 = fv_as_emb_typ fv_result  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____1627;
      FStar_TypeChecker_NBETerm.emb_typ = uu____1632
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____1663 =
      let uu____1664 = FStar_Syntax_Subst.compress t  in
      uu____1664.FStar_Syntax_Syntax.n  in
    match uu____1663 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____1671 ->
        (if w
         then
           (let uu____1673 =
              let uu____1678 =
                let uu____1679 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____1679
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1678)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1673)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1738,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1754,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____1769 ->
        ((let uu____1771 =
            let uu____1776 =
              let uu____1777 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____1777
               in
            (FStar_Errors.Warning_NotEmbedded, uu____1776)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1771);
         FStar_Pervasives_Native.None)
     in
  let uu____1778 = mkFV fv_direction [] []  in
  let uu____1783 = fv_as_emb_typ fv_direction  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____1778;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1783
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
    let uu____1812 =
      let uu____1813 = FStar_Syntax_Subst.compress t  in
      uu____1813.FStar_Syntax_Syntax.n  in
    match uu____1812 with
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
    | uu____1822 ->
        (if w
         then
           (let uu____1824 =
              let uu____1829 =
                let uu____1830 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____1830
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1829)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1824)
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1899,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1915,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1931,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1947,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____1962 -> FStar_Pervasives_Native.None  in
  let uu____1963 = mkFV fv_guard_policy [] []  in
  let uu____1968 = fv_as_emb_typ fv_guard_policy  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____1963;
    FStar_TypeChecker_NBETerm.emb_typ = uu____1968
  } 