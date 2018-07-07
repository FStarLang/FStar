open Prims
let mk_emb :
  'Auu____9 .
    (FStar_Range.range -> 'Auu____9 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'Auu____9 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____9 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____51 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____51
  
let embed :
  'Auu____97 .
    'Auu____97 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____97 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____117 = FStar_Syntax_Embeddings.embed e x  in
        uu____117 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____157 .
    Prims.bool ->
      'Auu____157 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____157 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____179 = FStar_Syntax_Embeddings.unembed e x  in
        uu____179 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____218 =
      let uu____219 = FStar_Syntax_Subst.compress t  in
      uu____219.FStar_Syntax_Syntax.n  in
    match uu____218 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____225;
          FStar_Syntax_Syntax.rng = uu____226;_}
        ->
        let uu____229 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____229
    | uu____230 ->
        (if w
         then
           (let uu____232 =
              let uu____237 =
                let uu____238 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____238  in
              (FStar_Errors.Warning_NotEmbedded, uu____237)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____232)
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
    let uu____268 =
      let uu____269 = FStar_Syntax_Subst.compress t  in
      uu____269.FStar_Syntax_Syntax.n  in
    match uu____268 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____275;
          FStar_Syntax_Syntax.rng = uu____276;_}
        ->
        let uu____279 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____279
    | uu____280 ->
        (if w
         then
           (let uu____282 =
              let uu____287 =
                let uu____288 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____288  in
              (FStar_Errors.Warning_NotEmbedded, uu____287)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____282)
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
          let uu____335 = f x  in
          FStar_Util.bind_opt uu____335
            (fun x1  ->
               let uu____343 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____343
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
        let uu____409 =
          mapM_opt
            (fun uu____422  ->
               match uu____422 with
               | (bv,e) ->
                   let uu____431 = unembed_term w e  in
                   FStar_Util.bind_opt uu____431
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____409
          (fun s  ->
             let uu____445 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____445)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____447 =
        let uu____448 = FStar_Syntax_Subst.compress t1  in
        uu____448.FStar_Syntax_Syntax.n  in
      match uu____447 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____459 ->
          (if w
           then
             (let uu____461 =
                let uu____466 =
                  let uu____467 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____467  in
                (FStar_Errors.Warning_NotEmbedded, uu____466)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____461)
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
      | FStar_Reflection_Data.Q_Meta t ->
          let uu____496 =
            let uu____501 =
              let uu____502 =
                let uu____511 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____511  in
              [uu____502]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____501
             in
          uu____496 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___230_530 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___230_530.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___230_530.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____549 = FStar_Syntax_Util.head_and_args t1  in
    match uu____549 with
    | (hd1,args) ->
        let uu____594 =
          let uu____609 =
            let uu____610 = FStar_Syntax_Util.un_uinst hd1  in
            uu____610.FStar_Syntax_Syntax.n  in
          (uu____609, args)  in
        (match uu____594 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____665)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____700 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____700
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____705 ->
             (if w
              then
                (let uu____721 =
                   let uu____726 =
                     let uu____727 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____727
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____726)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____721)
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
    let uu____759 =
      let uu____760 = FStar_Syntax_Subst.compress t  in
      uu____760.FStar_Syntax_Syntax.n  in
    match uu____759 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____766;
          FStar_Syntax_Syntax.rng = uu____767;_}
        ->
        let uu____770 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____770
    | uu____771 ->
        (if w
         then
           (let uu____773 =
              let uu____778 =
                let uu____779 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____779  in
              (FStar_Errors.Warning_NotEmbedded, uu____778)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____773)
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
    let uu____809 =
      let uu____810 = FStar_Syntax_Subst.compress t  in
      uu____810.FStar_Syntax_Syntax.n  in
    match uu____809 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____816;
          FStar_Syntax_Syntax.rng = uu____817;_}
        ->
        let uu____820 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____820
    | uu____821 ->
        (if w
         then
           (let uu____823 =
              let uu____828 =
                let uu____829 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____829  in
              (FStar_Errors.Warning_NotEmbedded, uu____828)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____823)
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
    let uu____859 =
      let uu____860 = FStar_Syntax_Subst.compress t  in
      uu____860.FStar_Syntax_Syntax.n  in
    match uu____859 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____866;
          FStar_Syntax_Syntax.rng = uu____867;_}
        ->
        let uu____870 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____870
    | uu____871 ->
        (if w
         then
           (let uu____873 =
              let uu____878 =
                let uu____879 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____879  in
              (FStar_Errors.Warning_NotEmbedded, uu____878)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____873)
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
          let uu____900 =
            let uu____905 =
              let uu____906 =
                let uu____915 =
                  let uu____916 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____916  in
                FStar_Syntax_Syntax.as_arg uu____915  in
              [uu____906]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____905
             in
          uu____900 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____936 =
            let uu____941 =
              let uu____942 =
                let uu____951 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____951  in
              [uu____942]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____941
             in
          uu____936 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___231_970 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___231_970.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___231_970.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____989 = FStar_Syntax_Util.head_and_args t1  in
    match uu____989 with
    | (hd1,args) ->
        let uu____1034 =
          let uu____1049 =
            let uu____1050 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1050.FStar_Syntax_Syntax.n  in
          (uu____1049, args)  in
        (match uu____1034 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1124)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1159 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1159
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1168)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1203 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1203
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1210 ->
             (if w
              then
                (let uu____1226 =
                   let uu____1231 =
                     let uu____1232 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1232
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1231)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1226)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1240  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1253 =
            let uu____1258 =
              let uu____1259 =
                let uu____1268 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1268  in
              [uu____1259]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1258
             in
          uu____1253 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1293 =
            let uu____1298 =
              let uu____1299 =
                let uu____1308 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1308  in
              let uu____1309 =
                let uu____1320 =
                  let uu____1329 =
                    let uu____1330 =
                      let uu____1335 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1335  in
                    embed uu____1330 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1329  in
                [uu____1320]  in
              uu____1299 :: uu____1309  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1298
             in
          uu____1293 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1367 =
            let uu____1372 =
              let uu____1373 =
                let uu____1382 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1382  in
              [uu____1373]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1372
             in
          uu____1367 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1402 =
            let uu____1407 =
              let uu____1408 =
                let uu____1417 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1417  in
              [uu____1408]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1407
             in
          uu____1402 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1438 =
            let uu____1443 =
              let uu____1444 =
                let uu____1453 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1453  in
              let uu____1454 =
                let uu____1465 =
                  let uu____1474 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1474  in
                [uu____1465]  in
              uu____1444 :: uu____1454  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1443
             in
          uu____1438 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1517 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1517 with
      | (hd1,args) ->
          let uu____1562 =
            let uu____1575 =
              let uu____1576 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1576.FStar_Syntax_Syntax.n  in
            (uu____1575, args)  in
          (match uu____1562 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1591)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1616 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1616
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1625)::(ps,uu____1627)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1662 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1662
                 (fun f1  ->
                    let uu____1668 =
                      let uu____1673 =
                        let uu____1678 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1678  in
                      unembed' w uu____1673 ps  in
                    FStar_Util.bind_opt uu____1668
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1695)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1720 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1720
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1729)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1754 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1754
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1763)::(t2,uu____1765)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1800 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1800
                 (fun bv1  ->
                    let uu____1806 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1806
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1813 ->
               (if w
                then
                  (let uu____1827 =
                     let uu____1832 =
                       let uu____1833 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1833
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1832)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1827)
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
    let uu____1852 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1852
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1866 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1866 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1888 =
            let uu____1893 =
              let uu____1894 =
                let uu____1903 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1903  in
              [uu____1894]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1893
             in
          uu____1888 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1923 =
            let uu____1928 =
              let uu____1929 =
                let uu____1938 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1938  in
              [uu____1929]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1928
             in
          uu____1923 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1958 =
            let uu____1963 =
              let uu____1964 =
                let uu____1973 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1973  in
              [uu____1964]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1963
             in
          uu____1958 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1994 =
            let uu____1999 =
              let uu____2000 =
                let uu____2009 =
                  let uu____2010 = e_term_aq aq  in embed uu____2010 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2009  in
              let uu____2013 =
                let uu____2024 =
                  let uu____2033 =
                    let uu____2034 = e_argv_aq aq  in embed uu____2034 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2033  in
                [uu____2024]  in
              uu____2000 :: uu____2013  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1999
             in
          uu____1994 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2073 =
            let uu____2078 =
              let uu____2079 =
                let uu____2088 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2088  in
              let uu____2089 =
                let uu____2100 =
                  let uu____2109 =
                    let uu____2110 = e_term_aq aq  in embed uu____2110 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2109  in
                [uu____2100]  in
              uu____2079 :: uu____2089  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2078
             in
          uu____2073 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2141 =
            let uu____2146 =
              let uu____2147 =
                let uu____2156 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2156  in
              let uu____2157 =
                let uu____2168 =
                  let uu____2177 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2177  in
                [uu____2168]  in
              uu____2147 :: uu____2157  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2146
             in
          uu____2141 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2205 =
            let uu____2210 =
              let uu____2211 =
                let uu____2220 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2220  in
              [uu____2211]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2210
             in
          uu____2205 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2241 =
            let uu____2246 =
              let uu____2247 =
                let uu____2256 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2256  in
              let uu____2257 =
                let uu____2268 =
                  let uu____2277 =
                    let uu____2278 = e_term_aq aq  in embed uu____2278 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2277  in
                [uu____2268]  in
              uu____2247 :: uu____2257  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2246
             in
          uu____2241 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2308 =
            let uu____2313 =
              let uu____2314 =
                let uu____2323 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2323  in
              [uu____2314]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2313
             in
          uu____2308 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2344 =
            let uu____2349 =
              let uu____2350 =
                let uu____2359 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2359  in
              let uu____2360 =
                let uu____2371 =
                  let uu____2380 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2380  in
                [uu____2371]  in
              uu____2350 :: uu____2360  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2349
             in
          uu____2344 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2415 =
            let uu____2420 =
              let uu____2421 =
                let uu____2430 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2430  in
              let uu____2431 =
                let uu____2442 =
                  let uu____2451 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2451  in
                let uu____2452 =
                  let uu____2463 =
                    let uu____2472 =
                      let uu____2473 = e_term_aq aq  in
                      embed uu____2473 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2472  in
                  let uu____2476 =
                    let uu____2487 =
                      let uu____2496 =
                        let uu____2497 = e_term_aq aq  in
                        embed uu____2497 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2496  in
                    [uu____2487]  in
                  uu____2463 :: uu____2476  in
                uu____2442 :: uu____2452  in
              uu____2421 :: uu____2431  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2420
             in
          uu____2415 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2548 =
            let uu____2553 =
              let uu____2554 =
                let uu____2563 =
                  let uu____2564 = e_term_aq aq  in embed uu____2564 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2563  in
              let uu____2567 =
                let uu____2578 =
                  let uu____2587 =
                    let uu____2588 =
                      let uu____2597 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2597  in
                    embed uu____2588 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2587  in
                [uu____2578]  in
              uu____2554 :: uu____2567  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2553
             in
          uu____2548 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2647 =
            let uu____2652 =
              let uu____2653 =
                let uu____2662 =
                  let uu____2663 = e_term_aq aq  in embed uu____2663 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2662  in
              let uu____2666 =
                let uu____2677 =
                  let uu____2686 =
                    let uu____2687 = e_term_aq aq  in embed uu____2687 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2686  in
                let uu____2690 =
                  let uu____2701 =
                    let uu____2710 =
                      let uu____2711 =
                        let uu____2716 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2716  in
                      embed uu____2711 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2710  in
                  [uu____2701]  in
                uu____2677 :: uu____2690  in
              uu____2653 :: uu____2666  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2652
             in
          uu____2647 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2762 =
            let uu____2767 =
              let uu____2768 =
                let uu____2777 =
                  let uu____2778 = e_term_aq aq  in embed uu____2778 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2777  in
              let uu____2781 =
                let uu____2792 =
                  let uu____2801 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2801  in
                let uu____2802 =
                  let uu____2813 =
                    let uu____2822 =
                      let uu____2823 =
                        let uu____2828 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2828  in
                      embed uu____2823 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2822  in
                  [uu____2813]  in
                uu____2792 :: uu____2802  in
              uu____2768 :: uu____2781  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2767
             in
          uu____2762 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___232_2867 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___232_2867.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___232_2867.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2883 = FStar_Syntax_Util.head_and_args t  in
      match uu____2883 with
      | (hd1,args) ->
          let uu____2928 =
            let uu____2941 =
              let uu____2942 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2942.FStar_Syntax_Syntax.n  in
            (uu____2941, args)  in
          (match uu____2928 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2957)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2982 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2982
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2991)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3016 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3016
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3025)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3050 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3050
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3059)::(r,uu____3061)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3096 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3096
                 (fun l1  ->
                    let uu____3102 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3102
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3111)::(t1,uu____3113)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3148 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3148
                 (fun b1  ->
                    let uu____3154 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3154
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3163)::(t1,uu____3165)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3200 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3200
                 (fun b1  ->
                    let uu____3206 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3206
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3215)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3240 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3240
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3249)::(t1,uu____3251)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3286 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3286
                 (fun b1  ->
                    let uu____3292 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3292
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3301)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3326 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3326
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3335)::(l,uu____3337)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3372 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3372
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3383)::(b,uu____3385)::(t1,uu____3387)::(t2,uu____3389)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3444 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3444
                 (fun r1  ->
                    let uu____3450 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3450
                      (fun b1  ->
                         let uu____3456 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3456
                           (fun t11  ->
                              let uu____3462 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3462
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3471)::(brs,uu____3473)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3508 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3508
                 (fun t2  ->
                    let uu____3514 =
                      let uu____3519 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3519 brs  in
                    FStar_Util.bind_opt uu____3514
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3538)::(t1,uu____3540)::(tacopt,uu____3542)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3587 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3587
                 (fun e1  ->
                    let uu____3593 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3593
                      (fun t2  ->
                         let uu____3599 =
                           let uu____3604 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3604 tacopt  in
                         FStar_Util.bind_opt uu____3599
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3623)::(c,uu____3625)::(tacopt,uu____3627)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3672 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3672
                 (fun e1  ->
                    let uu____3678 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3678
                      (fun c1  ->
                         let uu____3684 =
                           let uu____3689 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3689 tacopt  in
                         FStar_Util.bind_opt uu____3684
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
           | uu____3723 ->
               (if w
                then
                  (let uu____3737 =
                     let uu____3742 =
                       let uu____3743 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3743
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3742)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3737)
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
    let uu____3766 =
      let uu____3771 =
        let uu____3772 =
          let uu____3781 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3781  in
        let uu____3782 =
          let uu____3793 =
            let uu____3802 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3802  in
          let uu____3803 =
            let uu____3814 =
              let uu____3823 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____3823  in
            [uu____3814]  in
          uu____3793 :: uu____3803  in
        uu____3772 :: uu____3782  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3771
       in
    uu____3766 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3874 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3874 with
    | (hd1,args) ->
        let uu____3919 =
          let uu____3932 =
            let uu____3933 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3933.FStar_Syntax_Syntax.n  in
          (uu____3932, args)  in
        (match uu____3919 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3948)::(idx,uu____3950)::(s,uu____3952)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____3997 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____3997
               (fun nm1  ->
                  let uu____4003 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4003
                    (fun idx1  ->
                       let uu____4009 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4009
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4016 ->
             (if w
              then
                (let uu____4030 =
                   let uu____4035 =
                     let uu____4036 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4036
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4035)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4030)
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
        let uu____4057 =
          let uu____4062 =
            let uu____4063 =
              let uu____4072 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4072  in
            let uu____4073 =
              let uu____4084 =
                let uu____4093 =
                  let uu____4094 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4094 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4093  in
              [uu____4084]  in
            uu____4063 :: uu____4073  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4062
           in
        uu____4057 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4132 =
          let uu____4137 =
            let uu____4138 =
              let uu____4147 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4147  in
            let uu____4148 =
              let uu____4159 =
                let uu____4168 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4168  in
              [uu____4159]  in
            uu____4138 :: uu____4148  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4137
           in
        uu____4132 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___233_4195 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___233_4195.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___233_4195.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4212 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4212 with
    | (hd1,args) ->
        let uu____4257 =
          let uu____4270 =
            let uu____4271 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4271.FStar_Syntax_Syntax.n  in
          (uu____4270, args)  in
        (match uu____4257 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4286)::(md,uu____4288)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4323 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4323
               (fun t3  ->
                  let uu____4329 =
                    let uu____4334 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4334 md  in
                  FStar_Util.bind_opt uu____4329
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4353)::(post,uu____4355)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4390 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4390
               (fun pre1  ->
                  let uu____4396 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4396
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
         | uu____4420 ->
             (if w
              then
                (let uu____4434 =
                   let uu____4439 =
                     let uu____4440 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4440
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4439)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4434)
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
    let uu___234_4460 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___234_4460.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___234_4460.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4479 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4479 with
    | (hd1,args) ->
        let uu____4524 =
          let uu____4539 =
            let uu____4540 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4540.FStar_Syntax_Syntax.n  in
          (uu____4539, args)  in
        (match uu____4524 with
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
         | uu____4612 ->
             (if w
              then
                (let uu____4628 =
                   let uu____4633 =
                     let uu____4634 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4634
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4633)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4628)
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
    let uu____4664 =
      let uu____4665 = FStar_Syntax_Subst.compress t  in
      uu____4665.FStar_Syntax_Syntax.n  in
    match uu____4664 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____4671;
          FStar_Syntax_Syntax.rng = uu____4672;_}
        ->
        let uu____4675 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4675
    | uu____4676 ->
        (if w
         then
           (let uu____4678 =
              let uu____4683 =
                let uu____4684 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4684
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4683)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4678)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____4737 uu____4738 =
    let uu____4760 =
      let uu____4765 = FStar_Ident.range_of_id i  in
      let uu____4766 = FStar_Ident.text_of_id i  in (uu____4765, uu____4766)
       in
    embed repr rng uu____4760  in
  let unembed_ident t w uu____4790 =
    let uu____4795 = unembed' w repr t  in
    match uu____4795 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4814 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4814
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____4819 =
    FStar_Syntax_Syntax.t_tuple2_of FStar_Syntax_Syntax.t_range
      FStar_Syntax_Syntax.t_string
     in
  let uu____4820 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident uu____4819
    FStar_Ident.text_of_id uu____4820
  
let (e_univ_name :
  FStar_Syntax_Syntax.univ_name FStar_Syntax_Embeddings.embedding) = e_ident 
let (e_univ_names :
  FStar_Syntax_Syntax.univ_name Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_univ_name 
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,univs1,ty,t) ->
        let uu____4853 =
          let uu____4858 =
            let uu____4859 =
              let uu____4868 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____4868  in
            let uu____4869 =
              let uu____4880 =
                let uu____4889 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____4889  in
              let uu____4890 =
                let uu____4901 =
                  let uu____4910 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____4910  in
                let uu____4913 =
                  let uu____4924 =
                    let uu____4933 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____4933  in
                  let uu____4934 =
                    let uu____4945 =
                      let uu____4954 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____4954  in
                    [uu____4945]  in
                  uu____4924 :: uu____4934  in
                uu____4901 :: uu____4913  in
              uu____4880 :: uu____4890  in
            uu____4859 :: uu____4869  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4858
           in
        uu____4853 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5007 =
          let uu____5012 =
            let uu____5013 =
              let uu____5022 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5022  in
            let uu____5025 =
              let uu____5036 =
                let uu____5045 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5045  in
              [uu____5036]  in
            uu____5013 :: uu____5025  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5012
           in
        uu____5007 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5089 =
          let uu____5094 =
            let uu____5095 =
              let uu____5104 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5104  in
            let uu____5107 =
              let uu____5118 =
                let uu____5127 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5127  in
              let uu____5130 =
                let uu____5141 =
                  let uu____5150 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5150  in
                let uu____5151 =
                  let uu____5162 =
                    let uu____5171 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5171  in
                  let uu____5172 =
                    let uu____5183 =
                      let uu____5192 =
                        let uu____5193 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5193 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5192  in
                    [uu____5183]  in
                  uu____5162 :: uu____5172  in
                uu____5141 :: uu____5151  in
              uu____5118 :: uu____5130  in
            uu____5095 :: uu____5107  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5094
           in
        uu____5089 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___235_5256 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___235_5256.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___235_5256.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5273 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5273 with
    | (hd1,args) ->
        let uu____5318 =
          let uu____5331 =
            let uu____5332 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5332.FStar_Syntax_Syntax.n  in
          (uu____5331, args)  in
        (match uu____5318 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5347)::(us,uu____5349)::(bs,uu____5351)::(t2,uu____5353)::
            (dcs,uu____5355)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5420 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5420
               (fun nm1  ->
                  let uu____5434 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5434
                    (fun us1  ->
                       let uu____5448 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5448
                         (fun bs1  ->
                            let uu____5454 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5454
                              (fun t3  ->
                                 let uu____5460 =
                                   let uu____5467 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5467 dcs  in
                                 FStar_Util.bind_opt uu____5460
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_42  ->
                                           FStar_Pervasives_Native.Some _0_42)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5500)::(fvar1,uu____5502)::(univs1,uu____5504)::
            (ty,uu____5506)::(t2,uu____5508)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5573 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5573
               (fun r1  ->
                  let uu____5579 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5579
                    (fun fvar2  ->
                       let uu____5585 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5585
                         (fun univs2  ->
                            let uu____5599 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____5599
                              (fun ty1  ->
                                 let uu____5605 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____5605
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _0_43  ->
                                           FStar_Pervasives_Native.Some _0_43)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____5629 ->
             (if w
              then
                (let uu____5643 =
                   let uu____5648 =
                     let uu____5649 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5649
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5648)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5643)
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
          let uu____5670 =
            let uu____5675 =
              let uu____5676 =
                let uu____5685 =
                  let uu____5686 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5686  in
                FStar_Syntax_Syntax.as_arg uu____5685  in
              [uu____5676]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5675
             in
          uu____5670 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5707 =
            let uu____5712 =
              let uu____5713 =
                let uu____5722 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5722  in
              let uu____5723 =
                let uu____5734 =
                  let uu____5743 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5743  in
                [uu____5734]  in
              uu____5713 :: uu____5723  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5712
             in
          uu____5707 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___236_5770 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___236_5770.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___236_5770.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5789 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5789 with
    | (hd1,args) ->
        let uu____5834 =
          let uu____5847 =
            let uu____5848 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5848.FStar_Syntax_Syntax.n  in
          (uu____5847, args)  in
        (match uu____5834 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5878)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5903 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____5903
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____5912)::(e2,uu____5914)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____5949 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____5949
               (fun e11  ->
                  let uu____5955 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____5955
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____5962 ->
             (if w
              then
                (let uu____5976 =
                   let uu____5981 =
                     let uu____5982 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____5982
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5981)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5976)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp 
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv 
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_Syntax_Embeddings.embedding) = e_term 
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_attribute 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5998 =
      let uu____6003 =
        let uu____6004 =
          let uu____6013 =
            let uu____6014 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____6014  in
          FStar_Syntax_Syntax.as_arg uu____6013  in
        [uu____6004]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____6003
       in
    uu____5998 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6039 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____6039 with
    | (bv,aq) ->
        let uu____6046 =
          let uu____6051 =
            let uu____6052 =
              let uu____6061 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____6061  in
            let uu____6062 =
              let uu____6073 =
                let uu____6082 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____6082  in
              [uu____6073]  in
            uu____6052 :: uu____6062  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____6051
           in
        uu____6046 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6115 =
      let uu____6120 =
        let uu____6121 =
          let uu____6130 =
            let uu____6131 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____6136 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____6131 i.FStar_Syntax_Syntax.rng uu____6136  in
          FStar_Syntax_Syntax.as_arg uu____6130  in
        [uu____6121]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____6120
       in
    uu____6115 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6165 =
      let uu____6170 =
        let uu____6171 =
          let uu____6180 =
            let uu____6181 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____6181  in
          FStar_Syntax_Syntax.as_arg uu____6180  in
        [uu____6171]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____6170
       in
    uu____6165 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6211 =
      let uu____6216 =
        let uu____6217 =
          let uu____6226 =
            let uu____6227 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____6227  in
          FStar_Syntax_Syntax.as_arg uu____6226  in
        [uu____6217]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6216
       in
    uu____6211 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  