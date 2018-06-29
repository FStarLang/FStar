open Prims
let mk_emb :
  'Auu____9 .
    (FStar_Range.range -> 'Auu____9 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'Auu____9 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.typ ->
          'Auu____9 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) t
  
let embed :
  'Auu____96 .
    'Auu____96 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____96 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____116 = FStar_Syntax_Embeddings.embed e x  in
        uu____116 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____156 .
    Prims.bool ->
      'Auu____156 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____156 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____178 = FStar_Syntax_Embeddings.unembed e x  in
        uu____178 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____217 =
      let uu____218 = FStar_Syntax_Subst.compress t  in
      uu____218.FStar_Syntax_Syntax.n  in
    match uu____217 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____224;
          FStar_Syntax_Syntax.rng = uu____225;_}
        ->
        let uu____228 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____228
    | uu____229 ->
        (if w
         then
           (let uu____231 =
              let uu____236 =
                let uu____237 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____237  in
              (FStar_Errors.Warning_NotEmbedded, uu____236)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____231)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv 
let (e_binder : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding)
  =
  let embed_binder rng b =
    FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng)
     in
  let unembed_binder w t =
    let uu____267 =
      let uu____268 = FStar_Syntax_Subst.compress t  in
      uu____268.FStar_Syntax_Syntax.n  in
    match uu____267 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____274;
          FStar_Syntax_Syntax.rng = uu____275;_}
        ->
        let uu____278 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____278
    | uu____279 ->
        (if w
         then
           (let uu____281 =
              let uu____286 =
                let uu____287 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____287  in
              (FStar_Errors.Warning_NotEmbedded, uu____286)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____281)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_binder unembed_binder FStar_Reflection_Data.fstar_refl_binder 
let rec mapM_opt :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> FStar_Pervasives_Native.Some []
      | x::xs ->
          let uu____334 = f x  in
          FStar_Util.bind_opt uu____334
            (fun x1  ->
               let uu____342 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____342
                 (fun xs1  -> FStar_Pervasives_Native.Some (x1 :: xs1)))
  
let (e_term_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term rng t =
      let qi =
        {
          FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
          FStar_Syntax_Syntax.antiquotes = aq
        }  in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (t, qi))
        FStar_Pervasives_Native.None rng
       in
    let rec unembed_term w t =
      let apply_antiquotes t1 aq1 =
        let uu____408 =
          mapM_opt
            (fun uu____425  ->
               match uu____425 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____448 = unembed_term w e  in
                      FStar_Util.bind_opt uu____448
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1))))) aq1
           in
        FStar_Util.bind_opt uu____408
          (fun s  ->
             let uu____462 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____462)
         in
      let uu____463 =
        let uu____464 = FStar_Syntax_Subst.compress t  in
        uu____464.FStar_Syntax_Syntax.n  in
      match uu____463 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____475 ->
          (if w
           then
             (let uu____477 =
                let uu____482 =
                  let uu____483 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____483  in
                (FStar_Errors.Warning_NotEmbedded, uu____482)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____477)
           else ();
           FStar_Pervasives_Native.None)
       in
    mk_emb embed_term unembed_term FStar_Syntax_Syntax.t_term
  
let (e_term : FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding) =
  e_term_aq [] 
let (e_aqualv :
  FStar_Reflection_Data.aqualv FStar_Syntax_Embeddings.embedding) =
  let embed_aqualv rng q =
    let r =
      match q with
      | FStar_Reflection_Data.Q_Explicit  ->
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Q_Implicit  ->
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.t
       in
    let uu___225_513 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___225_513.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___225_513.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____532 = FStar_Syntax_Util.head_and_args t1  in
    match uu____532 with
    | (hd1,args) ->
        let uu____577 =
          let uu____592 =
            let uu____593 = FStar_Syntax_Util.un_uinst hd1  in
            uu____593.FStar_Syntax_Syntax.n  in
          (uu____592, args)  in
        (match uu____577 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____646 ->
             (if w
              then
                (let uu____662 =
                   let uu____667 =
                     let uu____668 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____668
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____667)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____662)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_aqualv unembed_aqualv FStar_Reflection_Data.fstar_refl_aqualv 
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_list e_binder 
let (e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings.embedding) =
  let embed_fv rng fv =
    FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
     in
  let unembed_fv w t =
    let uu____700 =
      let uu____701 = FStar_Syntax_Subst.compress t  in
      uu____701.FStar_Syntax_Syntax.n  in
    match uu____700 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____707;
          FStar_Syntax_Syntax.rng = uu____708;_}
        ->
        let uu____711 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____711
    | uu____712 ->
        (if w
         then
           (let uu____714 =
              let uu____719 =
                let uu____720 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____720  in
              (FStar_Errors.Warning_NotEmbedded, uu____719)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____714)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv 
let (e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding) =
  let embed_comp rng c =
    FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng)
     in
  let unembed_comp w t =
    let uu____750 =
      let uu____751 = FStar_Syntax_Subst.compress t  in
      uu____751.FStar_Syntax_Syntax.n  in
    match uu____750 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____757;
          FStar_Syntax_Syntax.rng = uu____758;_}
        ->
        let uu____761 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____761
    | uu____762 ->
        (if w
         then
           (let uu____764 =
              let uu____769 =
                let uu____770 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____770  in
              (FStar_Errors.Warning_NotEmbedded, uu____769)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____764)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp 
let (e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding) =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng)
     in
  let unembed_env w t =
    let uu____800 =
      let uu____801 = FStar_Syntax_Subst.compress t  in
      uu____801.FStar_Syntax_Syntax.n  in
    match uu____800 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____807;
          FStar_Syntax_Syntax.rng = uu____808;_}
        ->
        let uu____811 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____811
    | uu____812 ->
        (if w
         then
           (let uu____814 =
              let uu____819 =
                let uu____820 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____820  in
              (FStar_Errors.Warning_NotEmbedded, uu____819)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____814)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_env unembed_env FStar_Reflection_Data.fstar_refl_env 
let (e_const :
  FStar_Reflection_Data.vconst FStar_Syntax_Embeddings.embedding) =
  let embed_const rng c =
    let r =
      match c with
      | FStar_Reflection_Data.C_Unit  ->
          FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_True  ->
          FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_False  ->
          FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Int i ->
          let uu____841 =
            let uu____846 =
              let uu____847 =
                let uu____856 =
                  let uu____857 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____857  in
                FStar_Syntax_Syntax.as_arg uu____856  in
              [uu____847]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____846
             in
          uu____841 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____877 =
            let uu____882 =
              let uu____883 =
                let uu____892 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____892  in
              [uu____883]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____882
             in
          uu____877 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___226_911 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___226_911.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___226_911.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____930 = FStar_Syntax_Util.head_and_args t1  in
    match uu____930 with
    | (hd1,args) ->
        let uu____975 =
          let uu____990 =
            let uu____991 = FStar_Syntax_Util.un_uinst hd1  in
            uu____991.FStar_Syntax_Syntax.n  in
          (uu____990, args)  in
        (match uu____975 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1065)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1100 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1100
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1109)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1144 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1144
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1151 ->
             (if w
              then
                (let uu____1167 =
                   let uu____1172 =
                     let uu____1173 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1173
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1172)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1167)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1181  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1194 =
            let uu____1199 =
              let uu____1200 =
                let uu____1209 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1209  in
              [uu____1200]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1199
             in
          uu____1194 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1234 =
            let uu____1239 =
              let uu____1240 =
                let uu____1249 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1249  in
              let uu____1250 =
                let uu____1261 =
                  let uu____1270 =
                    let uu____1271 =
                      let uu____1276 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1276  in
                    embed uu____1271 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1270  in
                [uu____1261]  in
              uu____1240 :: uu____1250  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1239
             in
          uu____1234 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1308 =
            let uu____1313 =
              let uu____1314 =
                let uu____1323 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1323  in
              [uu____1314]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1313
             in
          uu____1308 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1343 =
            let uu____1348 =
              let uu____1349 =
                let uu____1358 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1358  in
              [uu____1349]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1348
             in
          uu____1343 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1379 =
            let uu____1384 =
              let uu____1385 =
                let uu____1394 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1394  in
              let uu____1395 =
                let uu____1406 =
                  let uu____1415 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1415  in
                [uu____1406]  in
              uu____1385 :: uu____1395  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1384
             in
          uu____1379 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1458 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1458 with
      | (hd1,args) ->
          let uu____1503 =
            let uu____1516 =
              let uu____1517 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1517.FStar_Syntax_Syntax.n  in
            (uu____1516, args)  in
          (match uu____1503 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1532)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1557 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1557
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1566)::(ps,uu____1568)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1603 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1603
                 (fun f1  ->
                    let uu____1609 =
                      let uu____1614 =
                        let uu____1619 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1619  in
                      unembed' w uu____1614 ps  in
                    FStar_Util.bind_opt uu____1609
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1636)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1661 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1661
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1670)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1695 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1695
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1704)::(t2,uu____1706)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1741 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1741
                 (fun bv1  ->
                    let uu____1747 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1747
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1754 ->
               (if w
                then
                  (let uu____1768 =
                     let uu____1773 =
                       let uu____1774 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1774
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1773)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1768)
                else ();
                FStar_Pervasives_Native.None))
       in
    mk_emb embed_pattern unembed_pattern
      FStar_Reflection_Data.fstar_refl_pattern
  
let (e_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  e_pattern' () 
let (e_branch :
  FStar_Reflection_Data.branch FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_pattern e_term 
let (e_argv : FStar_Reflection_Data.argv FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_term e_aqualv 
let (e_branch_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1793 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1793
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1807 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1807 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1829 =
            let uu____1834 =
              let uu____1835 =
                let uu____1844 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1844  in
              [uu____1835]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1834
             in
          uu____1829 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1864 =
            let uu____1869 =
              let uu____1870 =
                let uu____1879 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1879  in
              [uu____1870]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1869
             in
          uu____1864 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1899 =
            let uu____1904 =
              let uu____1905 =
                let uu____1914 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1914  in
              [uu____1905]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1904
             in
          uu____1899 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1935 =
            let uu____1940 =
              let uu____1941 =
                let uu____1950 =
                  let uu____1951 = e_term_aq aq  in embed uu____1951 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____1950  in
              let uu____1954 =
                let uu____1965 =
                  let uu____1974 =
                    let uu____1975 = e_argv_aq aq  in embed uu____1975 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____1974  in
                [uu____1965]  in
              uu____1941 :: uu____1954  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1940
             in
          uu____1935 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2014 =
            let uu____2019 =
              let uu____2020 =
                let uu____2029 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2029  in
              let uu____2030 =
                let uu____2041 =
                  let uu____2050 =
                    let uu____2051 = e_term_aq aq  in embed uu____2051 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2050  in
                [uu____2041]  in
              uu____2020 :: uu____2030  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2019
             in
          uu____2014 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2082 =
            let uu____2087 =
              let uu____2088 =
                let uu____2097 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2097  in
              let uu____2098 =
                let uu____2109 =
                  let uu____2118 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2118  in
                [uu____2109]  in
              uu____2088 :: uu____2098  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2087
             in
          uu____2082 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2146 =
            let uu____2151 =
              let uu____2152 =
                let uu____2161 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2161  in
              [uu____2152]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2151
             in
          uu____2146 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2182 =
            let uu____2187 =
              let uu____2188 =
                let uu____2197 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2197  in
              let uu____2198 =
                let uu____2209 =
                  let uu____2218 =
                    let uu____2219 = e_term_aq aq  in embed uu____2219 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2218  in
                [uu____2209]  in
              uu____2188 :: uu____2198  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2187
             in
          uu____2182 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2249 =
            let uu____2254 =
              let uu____2255 =
                let uu____2264 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2264  in
              [uu____2255]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2254
             in
          uu____2249 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2285 =
            let uu____2290 =
              let uu____2291 =
                let uu____2300 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2300  in
              let uu____2301 =
                let uu____2312 =
                  let uu____2321 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2321  in
                [uu____2312]  in
              uu____2291 :: uu____2301  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2290
             in
          uu____2285 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2356 =
            let uu____2361 =
              let uu____2362 =
                let uu____2371 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2371  in
              let uu____2372 =
                let uu____2383 =
                  let uu____2392 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2392  in
                let uu____2393 =
                  let uu____2404 =
                    let uu____2413 =
                      let uu____2414 = e_term_aq aq  in
                      embed uu____2414 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2413  in
                  let uu____2417 =
                    let uu____2428 =
                      let uu____2437 =
                        let uu____2438 = e_term_aq aq  in
                        embed uu____2438 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2437  in
                    [uu____2428]  in
                  uu____2404 :: uu____2417  in
                uu____2383 :: uu____2393  in
              uu____2362 :: uu____2372  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2361
             in
          uu____2356 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2489 =
            let uu____2494 =
              let uu____2495 =
                let uu____2504 =
                  let uu____2505 = e_term_aq aq  in embed uu____2505 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2504  in
              let uu____2508 =
                let uu____2519 =
                  let uu____2528 =
                    let uu____2529 =
                      let uu____2538 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2538  in
                    embed uu____2529 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2528  in
                [uu____2519]  in
              uu____2495 :: uu____2508  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2494
             in
          uu____2489 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2588 =
            let uu____2593 =
              let uu____2594 =
                let uu____2603 =
                  let uu____2604 = e_term_aq aq  in embed uu____2604 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2603  in
              let uu____2607 =
                let uu____2618 =
                  let uu____2627 =
                    let uu____2628 = e_term_aq aq  in embed uu____2628 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2627  in
                let uu____2631 =
                  let uu____2642 =
                    let uu____2651 =
                      let uu____2652 =
                        let uu____2657 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2657  in
                      embed uu____2652 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2651  in
                  [uu____2642]  in
                uu____2618 :: uu____2631  in
              uu____2594 :: uu____2607  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2593
             in
          uu____2588 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2703 =
            let uu____2708 =
              let uu____2709 =
                let uu____2718 =
                  let uu____2719 = e_term_aq aq  in embed uu____2719 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2718  in
              let uu____2722 =
                let uu____2733 =
                  let uu____2742 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2742  in
                let uu____2743 =
                  let uu____2754 =
                    let uu____2763 =
                      let uu____2764 =
                        let uu____2769 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2769  in
                      embed uu____2764 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2763  in
                  [uu____2754]  in
                uu____2733 :: uu____2743  in
              uu____2709 :: uu____2722  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2708
             in
          uu____2703 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___227_2808 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___227_2808.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___227_2808.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2824 = FStar_Syntax_Util.head_and_args t  in
      match uu____2824 with
      | (hd1,args) ->
          let uu____2869 =
            let uu____2882 =
              let uu____2883 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2883.FStar_Syntax_Syntax.n  in
            (uu____2882, args)  in
          (match uu____2869 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2898)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2923 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2923
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2932)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____2957 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2957
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____2966)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____2991 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____2991
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3000)::(r,uu____3002)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3037 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3037
                 (fun l1  ->
                    let uu____3043 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3043
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3052)::(t1,uu____3054)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3089 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3089
                 (fun b1  ->
                    let uu____3095 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3095
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3104)::(t1,uu____3106)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3141 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3141
                 (fun b1  ->
                    let uu____3147 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3147
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3156)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3181 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3181
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3190)::(t1,uu____3192)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3227 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3227
                 (fun b1  ->
                    let uu____3233 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3233
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3242)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3267 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3267
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3276)::(l,uu____3278)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3313 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3313
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3324)::(b,uu____3326)::(t1,uu____3328)::(t2,uu____3330)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3385 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3385
                 (fun r1  ->
                    let uu____3391 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3391
                      (fun b1  ->
                         let uu____3397 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3397
                           (fun t11  ->
                              let uu____3403 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3403
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3412)::(brs,uu____3414)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3449 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3449
                 (fun t2  ->
                    let uu____3455 =
                      let uu____3460 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3460 brs  in
                    FStar_Util.bind_opt uu____3455
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3479)::(t1,uu____3481)::(tacopt,uu____3483)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3528 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3528
                 (fun e1  ->
                    let uu____3534 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3534
                      (fun t2  ->
                         let uu____3540 =
                           let uu____3545 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3545 tacopt  in
                         FStar_Util.bind_opt uu____3540
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3564)::(c,uu____3566)::(tacopt,uu____3568)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3613 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3613
                 (fun e1  ->
                    let uu____3619 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3619
                      (fun c1  ->
                         let uu____3625 =
                           let uu____3630 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3630 tacopt  in
                         FStar_Util.bind_opt uu____3625
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_36  ->
                                   FStar_Pervasives_Native.Some _0_36)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____3664 ->
               (if w
                then
                  (let uu____3678 =
                     let uu____3683 =
                       let uu____3684 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3684
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3683)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3678)
                else ();
                FStar_Pervasives_Native.None))
       in
    mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____3709 =
      let uu____3714 =
        let uu____3715 =
          let uu____3724 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3724  in
        let uu____3725 =
          let uu____3736 =
            let uu____3745 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3745  in
          let uu____3746 =
            let uu____3757 =
              let uu____3766 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____3766  in
            [uu____3757]  in
          uu____3736 :: uu____3746  in
        uu____3715 :: uu____3725  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3714
       in
    uu____3709 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3817 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3817 with
    | (hd1,args) ->
        let uu____3862 =
          let uu____3875 =
            let uu____3876 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3876.FStar_Syntax_Syntax.n  in
          (uu____3875, args)  in
        (match uu____3862 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3891)::(idx,uu____3893)::(s,uu____3895)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____3940 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____3940
               (fun nm1  ->
                  let uu____3946 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____3946
                    (fun idx1  ->
                       let uu____3952 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____3952
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____3959 ->
             (if w
              then
                (let uu____3973 =
                   let uu____3978 =
                     let uu____3979 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____3979
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3978)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3973)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding) =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____4000 =
          let uu____4005 =
            let uu____4006 =
              let uu____4015 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4015  in
            let uu____4016 =
              let uu____4027 =
                let uu____4036 =
                  let uu____4037 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4037 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4036  in
              [uu____4027]  in
            uu____4006 :: uu____4016  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4005
           in
        uu____4000 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4075 =
          let uu____4080 =
            let uu____4081 =
              let uu____4090 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4090  in
            let uu____4091 =
              let uu____4102 =
                let uu____4111 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4111  in
              [uu____4102]  in
            uu____4081 :: uu____4091  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4080
           in
        uu____4075 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___228_4138 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___228_4138.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___228_4138.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4155 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4155 with
    | (hd1,args) ->
        let uu____4200 =
          let uu____4213 =
            let uu____4214 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4214.FStar_Syntax_Syntax.n  in
          (uu____4213, args)  in
        (match uu____4200 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4229)::(md,uu____4231)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4266 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4266
               (fun t3  ->
                  let uu____4272 =
                    let uu____4277 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4277 md  in
                  FStar_Util.bind_opt uu____4272
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4296)::(post,uu____4298)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4333 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4333
               (fun pre1  ->
                  let uu____4339 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4339
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
               FStar_Reflection_Data.C_Unknown
         | uu____4363 ->
             (if w
              then
                (let uu____4377 =
                   let uu____4382 =
                     let uu____4383 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4383
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4382)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4377)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_comp_view unembed_comp_view
    FStar_Reflection_Data.fstar_refl_comp_view
  
let (e_order : FStar_Order.order FStar_Syntax_Embeddings.embedding) =
  let embed_order rng o =
    let r =
      match o with
      | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
      | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
      | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt  in
    let uu___229_4403 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___229_4403.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___229_4403.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4422 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4422 with
    | (hd1,args) ->
        let uu____4467 =
          let uu____4482 =
            let uu____4483 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4483.FStar_Syntax_Syntax.n  in
          (uu____4482, args)  in
        (match uu____4467 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Gt
         | uu____4555 ->
             (if w
              then
                (let uu____4571 =
                   let uu____4576 =
                     let uu____4577 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4577
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4576)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4571)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_order unembed_order FStar_Syntax_Syntax.t_order 
let (e_sigelt : FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings.embedding)
  =
  let embed_sigelt rng se =
    FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng)
     in
  let unembed_sigelt w t =
    let uu____4607 =
      let uu____4608 = FStar_Syntax_Subst.compress t  in
      uu____4608.FStar_Syntax_Syntax.n  in
    match uu____4607 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____4614;
          FStar_Syntax_Syntax.rng = uu____4615;_}
        ->
        let uu____4618 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4618
    | uu____4619 ->
        (if w
         then
           (let uu____4621 =
              let uu____4626 =
                let uu____4627 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4627
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4626)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4621)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,ty,t) ->
        let uu____4646 =
          let uu____4651 =
            let uu____4652 =
              let uu____4661 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____4661  in
            let uu____4662 =
              let uu____4673 =
                let uu____4682 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____4682  in
              let uu____4683 =
                let uu____4694 =
                  let uu____4703 = embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____4703  in
                let uu____4704 =
                  let uu____4715 =
                    let uu____4724 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____4724  in
                  [uu____4715]  in
                uu____4694 :: uu____4704  in
              uu____4673 :: uu____4683  in
            uu____4652 :: uu____4662  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4651
           in
        uu____4646 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4769 =
          let uu____4774 =
            let uu____4775 =
              let uu____4784 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____4784  in
            let uu____4787 =
              let uu____4798 =
                let uu____4807 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____4807  in
              [uu____4798]  in
            uu____4775 :: uu____4787  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____4774
           in
        uu____4769 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____4846 =
          let uu____4851 =
            let uu____4852 =
              let uu____4861 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____4861  in
            let uu____4864 =
              let uu____4875 =
                let uu____4884 = embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____4884  in
              let uu____4885 =
                let uu____4896 =
                  let uu____4905 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____4905  in
                let uu____4906 =
                  let uu____4917 =
                    let uu____4926 =
                      let uu____4927 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      embed uu____4927 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____4926  in
                  [uu____4917]  in
                uu____4896 :: uu____4906  in
              uu____4875 :: uu____4885  in
            uu____4852 :: uu____4864  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____4851
           in
        uu____4846 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___230_4982 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___230_4982.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___230_4982.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4999 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4999 with
    | (hd1,args) ->
        let uu____5044 =
          let uu____5057 =
            let uu____5058 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5058.FStar_Syntax_Syntax.n  in
          (uu____5057, args)  in
        (match uu____5044 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5073)::(bs,uu____5075)::(t2,uu____5077)::(dcs,uu____5079)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5134 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5134
               (fun nm1  ->
                  let uu____5148 = unembed' w e_binders bs  in
                  FStar_Util.bind_opt uu____5148
                    (fun bs1  ->
                       let uu____5154 = unembed' w e_term t2  in
                       FStar_Util.bind_opt uu____5154
                         (fun t3  ->
                            let uu____5160 =
                              let uu____5167 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_string_list
                                 in
                              unembed' w uu____5167 dcs  in
                            FStar_Util.bind_opt uu____5160
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_42  ->
                                      FStar_Pervasives_Native.Some _0_42)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5198)::(fvar1,uu____5200)::(ty,uu____5202)::(t2,uu____5204)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5259 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5259
               (fun r1  ->
                  let uu____5265 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5265
                    (fun fvar2  ->
                       let uu____5271 = unembed' w e_term ty  in
                       FStar_Util.bind_opt uu____5271
                         (fun ty1  ->
                            let uu____5277 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5277
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____5299 ->
             (if w
              then
                (let uu____5313 =
                   let uu____5318 =
                     let uu____5319 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5319
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5318)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5313)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_Data.fstar_refl_sigelt_view
  
let (e_exp : FStar_Reflection_Data.exp FStar_Syntax_Embeddings.embedding) =
  let rec embed_exp rng e =
    let r =
      match e with
      | FStar_Reflection_Data.Unit  ->
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Var i ->
          let uu____5340 =
            let uu____5345 =
              let uu____5346 =
                let uu____5355 =
                  let uu____5356 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5356  in
                FStar_Syntax_Syntax.as_arg uu____5355  in
              [uu____5346]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5345
             in
          uu____5340 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5377 =
            let uu____5382 =
              let uu____5383 =
                let uu____5392 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5392  in
              let uu____5393 =
                let uu____5404 =
                  let uu____5413 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5413  in
                [uu____5404]  in
              uu____5383 :: uu____5393  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5382
             in
          uu____5377 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___231_5440 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___231_5440.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___231_5440.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5459 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5459 with
    | (hd1,args) ->
        let uu____5504 =
          let uu____5517 =
            let uu____5518 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5518.FStar_Syntax_Syntax.n  in
          (uu____5517, args)  in
        (match uu____5504 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5548)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5573 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____5573
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____5582)::(e2,uu____5584)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____5619 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____5619
               (fun e11  ->
                  let uu____5625 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____5625
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____5632 ->
             (if w
              then
                (let uu____5646 =
                   let uu____5651 =
                     let uu____5652 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____5652
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5651)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5646)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp 
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5662 =
      let uu____5667 =
        let uu____5668 =
          let uu____5677 =
            let uu____5678 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____5678  in
          FStar_Syntax_Syntax.as_arg uu____5677  in
        [uu____5668]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____5667
       in
    uu____5662 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5703 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____5703 with
    | (bv,aq) ->
        let uu____5710 =
          let uu____5715 =
            let uu____5716 =
              let uu____5725 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____5725  in
            let uu____5726 =
              let uu____5737 =
                let uu____5746 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____5746  in
              [uu____5737]  in
            uu____5716 :: uu____5726  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____5715
           in
        uu____5710 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5779 =
      let uu____5784 =
        let uu____5785 =
          let uu____5794 =
            let uu____5795 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____5800 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____5795 i.FStar_Syntax_Syntax.rng uu____5800  in
          FStar_Syntax_Syntax.as_arg uu____5794  in
        [uu____5785]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____5784
       in
    uu____5779 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5829 =
      let uu____5834 =
        let uu____5835 =
          let uu____5844 =
            let uu____5845 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____5845  in
          FStar_Syntax_Syntax.as_arg uu____5844  in
        [uu____5835]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____5834
       in
    uu____5829 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5875 =
      let uu____5880 =
        let uu____5881 =
          let uu____5890 =
            let uu____5891 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____5891  in
          FStar_Syntax_Syntax.as_arg uu____5890  in
        [uu____5881]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____5880
       in
    uu____5875 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  