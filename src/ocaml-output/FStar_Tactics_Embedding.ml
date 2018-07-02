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
let (t_proofstate : FStar_Syntax_Syntax.term) =
  let uu____39 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.tconst uu____39 
let (fv_proofstate : FStar_Syntax_Syntax.fv) =
  let uu____40 = fstar_tactics_lid' ["Types"; "proofstate"]  in
  FStar_Syntax_Syntax.fvconst uu____40 
let (t_result_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Types"; "result"] 
let (t_result : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tconst t_result_lid 
let (fv_result : FStar_Syntax_Syntax.fv) =
  let uu____41 = fstar_tactics_lid' ["Types"; "result"]  in
  FStar_Syntax_Syntax.fvconst uu____41 
let (t_result_of :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____49 = let uu____60 = FStar_Syntax_Syntax.as_arg t  in [uu____60]
       in
    FStar_Syntax_Util.mk_app t_result uu____49
  
let (t_guard_policy : FStar_Syntax_Syntax.term) =
  let uu____85 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.tconst uu____85 
let (fv_guard_policy : FStar_Syntax_Syntax.fv) =
  let uu____86 = fstar_tactics_lid' ["Types"; "guard_policy"]  in
  FStar_Syntax_Syntax.fvconst uu____86 
let (t_direction : FStar_Syntax_Syntax.term) =
  let uu____87 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.tconst uu____87 
let (fv_direction : FStar_Syntax_Syntax.fv) =
  let uu____88 = fstar_tactics_lid' ["Types"; "direction"]  in
  FStar_Syntax_Syntax.fvconst uu____88 
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
        let uu____139 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> em r x)
          (fun x  -> fun w  -> fun _norm  -> un w x) uu____139
  
let embed :
  'Auu____185 .
    'Auu____185 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____185 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____205 = FStar_Syntax_Embeddings.embed e x  in
        uu____205 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____245 .
    Prims.bool ->
      'Auu____245 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____245 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____267 = FStar_Syntax_Embeddings.unembed e x  in
        uu____267 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_proofstate :
  FStar_Tactics_Types.proofstate FStar_Syntax_Embeddings.embedding) =
  let embed_proofstate rng ps =
    FStar_Syntax_Util.mk_lazy ps t_proofstate
      FStar_Syntax_Syntax.Lazy_proofstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_proofstate w t =
    let uu____306 =
      let uu____307 = FStar_Syntax_Subst.compress t  in
      uu____307.FStar_Syntax_Syntax.n  in
    match uu____306 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____313;
          FStar_Syntax_Syntax.rng = uu____314;_}
        ->
        let uu____317 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____317
    | uu____320 ->
        (if w
         then
           (let uu____322 =
              let uu____327 =
                let uu____328 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded proofstate: %s" uu____328
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____327)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____322)
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
  
let (e_proofstate_nbe :
  FStar_Tactics_Types.proofstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_proofstate ps =
    let li =
      let uu____414 = FStar_Dyn.mkdyn ps  in
      {
        FStar_Syntax_Syntax.blob = uu____414;
        FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate;
        FStar_Syntax_Syntax.ltyp = t_proofstate;
        FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
      }  in
    FStar_TypeChecker_NBETerm.Lazy li  in
  let unembed_proofstate t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_proofstate ;
          FStar_Syntax_Syntax.ltyp = uu____426;
          FStar_Syntax_Syntax.rng = uu____427;_}
        ->
        let uu____430 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____430
    | uu____433 ->
        ((let uu____435 =
            let uu____440 =
              let uu____441 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded NBE proofstate: %s"
                uu____441
               in
            (FStar_Errors.Warning_NotEmbedded, uu____440)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____435);
         FStar_Pervasives_Native.None)
     in
  let uu____442 = mkFV fv_proofstate [] []  in
  {
    FStar_TypeChecker_NBETerm.em = embed_proofstate;
    FStar_TypeChecker_NBETerm.un = unembed_proofstate;
    FStar_TypeChecker_NBETerm.typ = uu____442
  } 
let e_result :
  'a .
    'a FStar_Syntax_Embeddings.embedding ->
      'a FStar_Tactics_Result.__result FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    let embed_result res rng uu____507 uu____508 =
      match res with
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____534 =
            let uu____539 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____540 =
              let uu____541 =
                let uu____550 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____550  in
              let uu____551 =
                let uu____562 =
                  let uu____571 = embed ea rng a  in
                  FStar_Syntax_Syntax.as_arg uu____571  in
                let uu____572 =
                  let uu____583 =
                    let uu____592 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____592  in
                  [uu____583]  in
                uu____562 :: uu____572  in
              uu____541 :: uu____551  in
            FStar_Syntax_Syntax.mk_Tm_app uu____539 uu____540  in
          uu____534 FStar_Pervasives_Native.None rng
      | FStar_Tactics_Result.Failed (msg,ps) ->
          let uu____629 =
            let uu____634 =
              FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed_tm
                [FStar_Syntax_Syntax.U_zero]
               in
            let uu____635 =
              let uu____636 =
                let uu____645 = FStar_Syntax_Embeddings.type_of ea  in
                FStar_Syntax_Syntax.iarg uu____645  in
              let uu____646 =
                let uu____657 =
                  let uu____666 =
                    embed FStar_Syntax_Embeddings.e_string rng msg  in
                  FStar_Syntax_Syntax.as_arg uu____666  in
                let uu____667 =
                  let uu____678 =
                    let uu____687 = embed e_proofstate rng ps  in
                    FStar_Syntax_Syntax.as_arg uu____687  in
                  [uu____678]  in
                uu____657 :: uu____667  in
              uu____636 :: uu____646  in
            FStar_Syntax_Syntax.mk_Tm_app uu____634 uu____635  in
          uu____629 FStar_Pervasives_Native.None rng
       in
    let unembed_result t w uu____743 =
      let hd'_and_args tm =
        let tm1 = FStar_Syntax_Util.unascribe tm  in
        let uu____771 = FStar_Syntax_Util.head_and_args tm1  in
        match uu____771 with
        | (hd1,args) ->
            let uu____828 =
              let uu____829 = FStar_Syntax_Util.un_uinst hd1  in
              uu____829.FStar_Syntax_Syntax.n  in
            (uu____828, args)
         in
      let uu____842 = hd'_and_args t  in
      match uu____842 with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(a,uu____864)::(ps,uu____866)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____933 = unembed' w ea a  in
          FStar_Util.bind_opt uu____933
            (fun a1  ->
               let uu____941 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____941
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,_t::(msg,uu____953)::(ps,uu____955)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1022 = unembed' w FStar_Syntax_Embeddings.e_string msg
             in
          FStar_Util.bind_opt uu____1022
            (fun msg1  ->
               let uu____1030 = unembed' w e_proofstate ps  in
               FStar_Util.bind_opt uu____1030
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____1039 ->
          (if w
           then
             (let uu____1055 =
                let uu____1060 =
                  let uu____1061 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded tactic result: %s"
                    uu____1061
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____1060)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1055)
           else ();
           FStar_Pervasives_Native.None)
       in
    let uu____1065 =
      let uu____1066 = FStar_Syntax_Embeddings.type_of ea  in
      t_result_of uu____1066  in
    let uu____1067 =
      let uu____1068 =
        let uu____1075 =
          FStar_All.pipe_right t_result_lid FStar_Ident.string_of_lid  in
        let uu____1076 =
          let uu____1079 = FStar_Syntax_Embeddings.emb_typ_of ea  in
          [uu____1079]  in
        (uu____1075, uu____1076)  in
      FStar_Syntax_Syntax.ET_app uu____1068  in
    FStar_Syntax_Embeddings.mk_emb_full embed_result unembed_result
      uu____1065 (fun uu____1085  -> "") uu____1067
  
let e_result_nbe :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a FStar_Tactics_Result.__result FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    let embed_result res =
      match res with
      | FStar_Tactics_Result.Failed (msg,ps) ->
          let uu____1118 =
            let uu____1125 =
              let uu____1130 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1130  in
            let uu____1131 =
              let uu____1138 =
                let uu____1143 =
                  FStar_TypeChecker_NBETerm.embed
                    FStar_TypeChecker_NBETerm.e_string msg
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1143  in
              let uu____1144 =
                let uu____1151 =
                  let uu____1156 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe ps  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1156  in
                [uu____1151]  in
              uu____1138 :: uu____1144  in
            uu____1125 :: uu____1131  in
          mkConstruct fstar_tactics_Failed_fv [FStar_Syntax_Syntax.U_zero]
            uu____1118
      | FStar_Tactics_Result.Success (a,ps) ->
          let uu____1175 =
            let uu____1182 =
              let uu____1187 = FStar_TypeChecker_NBETerm.type_of ea  in
              FStar_TypeChecker_NBETerm.as_iarg uu____1187  in
            let uu____1188 =
              let uu____1195 =
                let uu____1200 = FStar_TypeChecker_NBETerm.embed ea a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1200  in
              let uu____1201 =
                let uu____1208 =
                  let uu____1213 =
                    FStar_TypeChecker_NBETerm.embed e_proofstate_nbe ps  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1213  in
                [uu____1208]  in
              uu____1195 :: uu____1201  in
            uu____1182 :: uu____1188  in
          mkConstruct fstar_tactics_Success_fv [FStar_Syntax_Syntax.U_zero]
            uu____1175
       in
    let unembed_result t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1245,(ps,uu____1247)::(a,uu____1249)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Success_lid ->
          let uu____1281 = FStar_TypeChecker_NBETerm.unembed ea a  in
          FStar_Util.bind_opt uu____1281
            (fun a1  ->
               let uu____1289 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe ps  in
               FStar_Util.bind_opt uu____1289
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Success (a1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1299,(ps,uu____1301)::(msg,uu____1303)::_t::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Failed_lid ->
          let uu____1335 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_string msg
             in
          FStar_Util.bind_opt uu____1335
            (fun msg1  ->
               let uu____1343 =
                 FStar_TypeChecker_NBETerm.unembed e_proofstate_nbe ps  in
               FStar_Util.bind_opt uu____1343
                 (fun ps1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Tactics_Result.Failed (msg1, ps1))))
      | uu____1352 -> FStar_Pervasives_Native.None  in
    let uu____1355 = mkFV fv_result [] []  in
    {
      FStar_TypeChecker_NBETerm.em = embed_result;
      FStar_TypeChecker_NBETerm.un = unembed_result;
      FStar_TypeChecker_NBETerm.typ = uu____1355
    }
  
let (e_direction :
  FStar_Tactics_Types.direction FStar_Syntax_Embeddings.embedding) =
  let embed_direction rng d =
    match d with
    | FStar_Tactics_Types.TopDown  -> fstar_tactics_topdown
    | FStar_Tactics_Types.BottomUp  -> fstar_tactics_bottomup  in
  let unembed_direction w t =
    let uu____1390 =
      let uu____1391 = FStar_Syntax_Subst.compress t  in
      uu____1391.FStar_Syntax_Syntax.n  in
    match uu____1390 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____1398 ->
        (if w
         then
           (let uu____1400 =
              let uu____1405 =
                let uu____1406 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded direction: %s" uu____1406
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1405)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1400)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_direction unembed_direction t_direction 
let (e_direction_nbe :
  FStar_Tactics_Types.direction FStar_TypeChecker_NBETerm.embedding) =
  let embed_direction res = failwith "e_direction_nbe"  in
  let unembed_direction t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1427,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_topdown_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.TopDown
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1443,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_bottomup_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.BottomUp
    | uu____1458 ->
        ((let uu____1460 =
            let uu____1465 =
              let uu____1466 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded direction: %s" uu____1466
               in
            (FStar_Errors.Warning_NotEmbedded, uu____1465)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1460);
         FStar_Pervasives_Native.None)
     in
  let uu____1467 = mkFV fv_direction [] []  in
  {
    FStar_TypeChecker_NBETerm.em = embed_direction;
    FStar_TypeChecker_NBETerm.un = unembed_direction;
    FStar_TypeChecker_NBETerm.typ = uu____1467
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
    let uu____1500 =
      let uu____1501 = FStar_Syntax_Subst.compress t  in
      uu____1501.FStar_Syntax_Syntax.n  in
    match uu____1500 with
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
    | uu____1510 ->
        (if w
         then
           (let uu____1512 =
              let uu____1517 =
                let uu____1518 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded guard_policy: %s"
                  uu____1518
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1517)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1512)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_guard_policy unembed_guard_policy t_guard_policy 
let (e_guard_policy_nbe :
  FStar_Tactics_Types.guard_policy FStar_TypeChecker_NBETerm.embedding) =
  let embed_guard_policy res = failwith "e_guard_policy_nbe"  in
  let unembed_guard_policy t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1541,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_SMT_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.SMT
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1557,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Goal_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Goal
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1573,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Force_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Force
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____1589,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_Drop_lid ->
        FStar_Pervasives_Native.Some FStar_Tactics_Types.Drop
    | uu____1604 -> FStar_Pervasives_Native.None  in
  let uu____1605 = mkFV fv_guard_policy [] []  in
  {
    FStar_TypeChecker_NBETerm.em = embed_guard_policy;
    FStar_TypeChecker_NBETerm.un = unembed_guard_policy;
    FStar_TypeChecker_NBETerm.typ = uu____1605
  } 