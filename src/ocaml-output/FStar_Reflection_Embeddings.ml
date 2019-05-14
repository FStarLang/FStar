open Prims
let mk_emb :
  'Auu____8 .
    (FStar_Range.range -> 'Auu____8 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'Auu____8 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____8 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____76 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____76
  
let embed :
  'Auu____113 .
    'Auu____113 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____113 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____137 = FStar_Syntax_Embeddings.embed e x  in
        uu____137 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____159 .
    Prims.bool ->
      'Auu____159 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____159 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____191 = FStar_Syntax_Embeddings.unembed e x  in
        uu____191 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____275 =
      let uu____276 = FStar_Syntax_Subst.compress t  in
      uu____276.FStar_Syntax_Syntax.n  in
    match uu____275 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____295;
          FStar_Syntax_Syntax.rng = uu____296;_}
        ->
        let uu____303 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____303
    | uu____324 ->
        (if w
         then
           (let uu____327 =
              let uu____333 =
                let uu____335 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____335  in
              (FStar_Errors.Warning_NotEmbedded, uu____333)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____327)
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
    let uu____398 =
      let uu____399 = FStar_Syntax_Subst.compress t  in
      uu____399.FStar_Syntax_Syntax.n  in
    match uu____398 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____413;
          FStar_Syntax_Syntax.rng = uu____414;_}
        ->
        let uu____421 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____421
    | uu____422 ->
        (if w
         then
           (let uu____425 =
              let uu____431 =
                let uu____433 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____433  in
              (FStar_Errors.Warning_NotEmbedded, uu____431)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____425)
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
          let uu____485 = f x  in
          FStar_Util.bind_opt uu____485
            (fun x1  ->
               let uu____493 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____493
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
        let uu____624 =
          mapM_opt
            (fun uu____646  ->
               match uu____646 with
               | (bv,e) ->
                   let uu____682 = unembed_term w e  in
                   FStar_Util.bind_opt uu____682
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____624
          (fun s  ->
             let uu____721 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____721)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____743 =
        let uu____744 = FStar_Syntax_Subst.compress t1  in
        uu____744.FStar_Syntax_Syntax.n  in
      match uu____743 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____779 ->
          (if w
           then
             (let uu____782 =
                let uu____788 =
                  let uu____790 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____790  in
                (FStar_Errors.Warning_NotEmbedded, uu____788)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____782)
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
          let uu____870 =
            let uu____875 =
              let uu____876 =
                let uu____889 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____889  in
              [uu____876]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____875
             in
          uu____870 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___88_926 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___88_926.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___88_926.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____971 = FStar_Syntax_Util.head_and_args t1  in
    match uu____971 with
    | (hd1,args) ->
        let uu____1040 =
          let uu____1059 =
            let uu____1060 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1060.FStar_Syntax_Syntax.n  in
          (uu____1059, args)  in
        (match uu____1040 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____1149)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____1207 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____1207
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____1228 ->
             (if w
              then
                (let uu____1249 =
                   let uu____1255 =
                     let uu____1257 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____1257
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1255)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1249)
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
    let uu____1331 =
      let uu____1332 = FStar_Syntax_Subst.compress t  in
      uu____1332.FStar_Syntax_Syntax.n  in
    match uu____1331 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____1349;
          FStar_Syntax_Syntax.rng = uu____1350;_}
        ->
        let uu____1357 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____1357
    | uu____1370 ->
        (if w
         then
           (let uu____1373 =
              let uu____1379 =
                let uu____1381 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____1381  in
              (FStar_Errors.Warning_NotEmbedded, uu____1379)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1373)
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
    let uu____1464 =
      let uu____1465 = FStar_Syntax_Subst.compress t  in
      uu____1465.FStar_Syntax_Syntax.n  in
    match uu____1464 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____1483;
          FStar_Syntax_Syntax.rng = uu____1484;_}
        ->
        let uu____1491 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____1491
    | uu____1508 ->
        (if w
         then
           (let uu____1511 =
              let uu____1517 =
                let uu____1519 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____1519  in
              (FStar_Errors.Warning_NotEmbedded, uu____1517)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1511)
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
    let uu____1904 =
      let uu____1905 = FStar_Syntax_Subst.compress t  in
      uu____1905.FStar_Syntax_Syntax.n  in
    match uu____1904 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____1973;
          FStar_Syntax_Syntax.rng = uu____1974;_}
        ->
        let uu____1981 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____1981
    | uu____2198 ->
        (if w
         then
           (let uu____2201 =
              let uu____2207 =
                let uu____2209 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____2209  in
              (FStar_Errors.Warning_NotEmbedded, uu____2207)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2201)
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
          let uu____2363 =
            let uu____2368 =
              let uu____2369 =
                let uu____2382 =
                  let uu____2391 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____2391  in
                FStar_Syntax_Syntax.as_arg uu____2382  in
              [uu____2369]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____2368
             in
          uu____2363 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____2419 =
            let uu____2424 =
              let uu____2425 =
                let uu____2438 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____2438  in
              [uu____2425]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____2424
             in
          uu____2419 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____2473 =
            let uu____2478 =
              let uu____2479 =
                let uu____2492 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2492  in
              [uu____2479]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____2478
             in
          uu____2473 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____2526 =
            let uu____2531 =
              let uu____2532 =
                let uu____2545 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____2545  in
              [uu____2532]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____2531
             in
          uu____2526 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___177_2581 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___177_2581.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___177_2581.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2626 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2626 with
    | (hd1,args) ->
        let uu____2695 =
          let uu____2714 =
            let uu____2715 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2715.FStar_Syntax_Syntax.n  in
          (uu____2714, args)  in
        (match uu____2695 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____2834)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____2892 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____2892
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _2899  -> FStar_Pervasives_Native.Some _2899)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____2902)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____2960 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____2960
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _2971  -> FStar_Pervasives_Native.Some _2971)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____2974)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____3032 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____3032
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _3039  -> FStar_Pervasives_Native.Some _3039)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _3072  -> FStar_Pervasives_Native.Some _3072)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____3075)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____3133 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____3133
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _3152  -> FStar_Pervasives_Native.Some _3152)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____3153 ->
             (if w
              then
                (let uu____3174 =
                   let uu____3180 =
                     let uu____3182 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____3182
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3180)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3174)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____3195  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____3216 =
            let uu____3221 =
              let uu____3222 =
                let uu____3235 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____3235  in
              [uu____3222]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____3221
             in
          uu____3216 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____3280 =
            let uu____3285 =
              let uu____3286 =
                let uu____3299 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____3299  in
              let uu____3311 =
                let uu____3326 =
                  let uu____3339 =
                    let uu____3348 =
                      let uu____3353 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____3353  in
                    embed uu____3348 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____3339  in
                [uu____3326]  in
              uu____3286 :: uu____3311  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____3285
             in
          uu____3280 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____3400 =
            let uu____3405 =
              let uu____3406 =
                let uu____3419 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____3419  in
              [uu____3406]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____3405
             in
          uu____3400 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____3463 =
            let uu____3468 =
              let uu____3469 =
                let uu____3482 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____3482  in
              [uu____3469]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____3468
             in
          uu____3463 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____3540 =
            let uu____3545 =
              let uu____3546 =
                let uu____3559 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____3559  in
              let uu____3573 =
                let uu____3588 =
                  let uu____3601 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____3601  in
                [uu____3588]  in
              uu____3546 :: uu____3573  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____3545
             in
          uu____3540 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____3684 = FStar_Syntax_Util.head_and_args t1  in
      match uu____3684 with
      | (hd1,args) ->
          let uu____3753 =
            let uu____3770 =
              let uu____3771 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3771.FStar_Syntax_Syntax.n  in
            (uu____3770, args)  in
          (match uu____3753 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3798)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____3846 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3846
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _3853  -> FStar_Pervasives_Native.Some _3853)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____3856)::(ps,uu____3858)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____3928 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3928
                 (fun f1  ->
                    let uu____3946 =
                      let uu____3951 =
                        let uu____3956 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____3956  in
                      unembed' w uu____3951 ps  in
                    FStar_Util.bind_opt uu____3946
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _3969  -> FStar_Pervasives_Native.Some _3969)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____3977)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____4025 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____4025
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _4052  -> FStar_Pervasives_Native.Some _4052)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____4055)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____4103 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____4103
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _4130  -> FStar_Pervasives_Native.Some _4130)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____4133)::(t2,uu____4135)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____4205 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____4205
                 (fun bv1  ->
                    let uu____4231 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____4231
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _4254  -> FStar_Pervasives_Native.Some _4254)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____4264 ->
               (if w
                then
                  (let uu____4283 =
                     let uu____4289 =
                       let uu____4291 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____4291
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4289)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____4283)
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
    (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____4330 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____4330
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____4357 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____4357 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____4399 =
            let uu____4404 =
              let uu____4405 =
                let uu____4418 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____4418  in
              [uu____4405]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____4404
             in
          uu____4399 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____4460 =
            let uu____4465 =
              let uu____4466 =
                let uu____4479 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____4479  in
              [uu____4466]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____4465
             in
          uu____4460 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____4523 =
            let uu____4528 =
              let uu____4529 =
                let uu____4542 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____4542  in
              [uu____4529]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____4528
             in
          uu____4523 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____4590 =
            let uu____4595 =
              let uu____4596 =
                let uu____4609 =
                  let uu____4618 = e_term_aq aq  in embed uu____4618 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____4609  in
              let uu____4629 =
                let uu____4644 =
                  let uu____4657 =
                    let uu____4666 = e_argv_aq aq  in embed uu____4666 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____4657  in
                [uu____4644]  in
              uu____4596 :: uu____4629  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____4595
             in
          uu____4590 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____4731 =
            let uu____4736 =
              let uu____4737 =
                let uu____4750 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____4750  in
              let uu____4759 =
                let uu____4774 =
                  let uu____4787 =
                    let uu____4796 = e_term_aq aq  in embed uu____4796 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____4787  in
                [uu____4774]  in
              uu____4737 :: uu____4759  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____4736
             in
          uu____4731 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____4853 =
            let uu____4858 =
              let uu____4859 =
                let uu____4872 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____4872  in
              let uu____4881 =
                let uu____4896 =
                  let uu____4909 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____4909  in
                [uu____4896]  in
              uu____4859 :: uu____4881  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____4858
             in
          uu____4853 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____4959 =
            let uu____4964 =
              let uu____4965 =
                let uu____4978 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____4978  in
              [uu____4965]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____4964
             in
          uu____4959 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____5031 =
            let uu____5036 =
              let uu____5037 =
                let uu____5050 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____5050  in
              let uu____5064 =
                let uu____5079 =
                  let uu____5092 =
                    let uu____5101 = e_term_aq aq  in embed uu____5101 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____5092  in
                [uu____5079]  in
              uu____5037 :: uu____5064  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____5036
             in
          uu____5031 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____5149 =
            let uu____5154 =
              let uu____5155 =
                let uu____5168 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____5168  in
              [uu____5155]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____5154
             in
          uu____5149 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____5203 =
            let uu____5208 =
              let uu____5209 =
                let uu____5222 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____5222  in
              let uu____5231 =
                let uu____5246 =
                  let uu____5259 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____5259  in
                [uu____5246]  in
              uu____5209 :: uu____5231  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____5208
             in
          uu____5203 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____5340 =
            let uu____5345 =
              let uu____5346 =
                let uu____5359 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____5359  in
              let uu____5369 =
                let uu____5384 =
                  let uu____5397 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____5397  in
                let uu____5411 =
                  let uu____5426 =
                    let uu____5439 =
                      let uu____5448 = e_term_aq aq  in
                      embed uu____5448 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____5439  in
                  let uu____5459 =
                    let uu____5474 =
                      let uu____5487 =
                        let uu____5496 = e_term_aq aq  in
                        embed uu____5496 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____5487  in
                    [uu____5474]  in
                  uu____5426 :: uu____5459  in
                uu____5384 :: uu____5411  in
              uu____5346 :: uu____5369  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____5345
             in
          uu____5340 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____5581 =
            let uu____5586 =
              let uu____5587 =
                let uu____5600 =
                  let uu____5609 = e_term_aq aq  in embed uu____5609 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____5600  in
              let uu____5620 =
                let uu____5635 =
                  let uu____5648 =
                    let uu____5657 =
                      let uu____5670 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____5670  in
                    embed uu____5657 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____5648  in
                [uu____5635]  in
              uu____5587 :: uu____5620  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____5586
             in
          uu____5581 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____5766 =
            let uu____5771 =
              let uu____5772 =
                let uu____5785 =
                  let uu____5794 = e_term_aq aq  in embed uu____5794 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____5785  in
              let uu____5805 =
                let uu____5820 =
                  let uu____5833 =
                    let uu____5842 = e_term_aq aq  in embed uu____5842 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____5833  in
                let uu____5853 =
                  let uu____5868 =
                    let uu____5881 =
                      let uu____5890 =
                        let uu____5899 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____5899  in
                      embed uu____5890 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____5881  in
                  [uu____5868]  in
                uu____5820 :: uu____5853  in
              uu____5772 :: uu____5805  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____5771
             in
          uu____5766 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____5995 =
            let uu____6000 =
              let uu____6001 =
                let uu____6014 =
                  let uu____6023 = e_term_aq aq  in embed uu____6023 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____6014  in
              let uu____6034 =
                let uu____6049 =
                  let uu____6062 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____6062  in
                let uu____6075 =
                  let uu____6090 =
                    let uu____6103 =
                      let uu____6112 =
                        let uu____6121 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____6121  in
                      embed uu____6112 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____6103  in
                  [uu____6090]  in
                uu____6049 :: uu____6075  in
              uu____6001 :: uu____6034  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____6000
             in
          uu____5995 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___370_6186 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___370_6186.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___370_6186.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____6220 = FStar_Syntax_Util.head_and_args t  in
      match uu____6220 with
      | (hd1,args) ->
          let uu____6289 =
            let uu____6306 =
              let uu____6307 = FStar_Syntax_Util.un_uinst hd1  in
              uu____6307.FStar_Syntax_Syntax.n  in
            (uu____6306, args)  in
          (match uu____6289 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____6334)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____6382 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____6382
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _6409  -> FStar_Pervasives_Native.Some _6409)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____6412)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____6460 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____6460
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _6487  -> FStar_Pervasives_Native.Some _6487)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____6490)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____6538 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____6538
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _6557  -> FStar_Pervasives_Native.Some _6557)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____6560)::(r,uu____6562)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____6632 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____6632
                 (fun l1  ->
                    let uu____6654 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____6654
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _6661  -> FStar_Pervasives_Native.Some _6661)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____6668)::(t1,uu____6670)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____6740 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____6740
                 (fun b1  ->
                    let uu____6746 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____6746
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _6769  -> FStar_Pervasives_Native.Some _6769)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____6776)::(t1,uu____6778)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____6848 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____6848
                 (fun b1  ->
                    let uu____6854 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____6854
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _6877  -> FStar_Pervasives_Native.Some _6877)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____6884)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____6932 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____6932
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _6939  -> FStar_Pervasives_Native.Some _6939)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____6942)::(t1,uu____6944)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____7014 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____7014
                 (fun b1  ->
                    let uu____7040 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____7040
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _7063  -> FStar_Pervasives_Native.Some _7063)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____7075)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____7123 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____7123
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _7130  -> FStar_Pervasives_Native.Some _7130)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____7133)::(l,uu____7135)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____7205 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____7205
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _7214  -> FStar_Pervasives_Native.Some _7214)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____7217)::(b,uu____7219)::(t1,uu____7221)::(t2,uu____7223)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____7337 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____7337
                 (fun r1  ->
                    let uu____7347 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____7347
                      (fun b1  ->
                         let uu____7373 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____7373
                           (fun t11  ->
                              let uu____7395 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____7395
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _7418  ->
                                        FStar_Pervasives_Native.Some _7418)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____7435)::(brs,uu____7437)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____7507 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____7507
                 (fun t2  ->
                    let uu____7529 =
                      let uu____7534 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____7534 brs  in
                    FStar_Util.bind_opt uu____7529
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _7549  -> FStar_Pervasives_Native.Some _7549)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____7558)::(t1,uu____7560)::(tacopt,uu____7562)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____7654 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____7654
                 (fun e1  ->
                    let uu____7676 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____7676
                      (fun t2  ->
                         let uu____7698 =
                           let uu____7707 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____7707 tacopt  in
                         FStar_Util.bind_opt uu____7698
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _7742  ->
                                   FStar_Pervasives_Native.Some _7742)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____7759)::(c,uu____7761)::(tacopt,uu____7763)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____7855 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____7855
                 (fun e1  ->
                    let uu____7877 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____7877
                      (fun c1  ->
                         let uu____7899 =
                           let uu____7908 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____7908 tacopt  in
                         FStar_Util.bind_opt uu____7899
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _7943  ->
                                   FStar_Pervasives_Native.Some _7943)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _7986  -> FStar_Pervasives_Native.Some _7986)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____7987 ->
               (if w
                then
                  (let uu____8006 =
                     let uu____8012 =
                       let uu____8014 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____8014
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____8012)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____8006)
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
    let uu____8069 =
      let uu____8074 =
        let uu____8075 =
          let uu____8088 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____8088  in
        let uu____8098 =
          let uu____8113 =
            let uu____8126 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____8126  in
          let uu____8135 =
            let uu____8150 =
              let uu____8163 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____8163  in
            [uu____8150]  in
          uu____8113 :: uu____8135  in
        uu____8075 :: uu____8098  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____8074
       in
    uu____8069 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____8264 = FStar_Syntax_Util.head_and_args t1  in
    match uu____8264 with
    | (hd1,args) ->
        let uu____8336 =
          let uu____8353 =
            let uu____8354 = FStar_Syntax_Util.un_uinst hd1  in
            uu____8354.FStar_Syntax_Syntax.n  in
          (uu____8353, args)  in
        (match uu____8336 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____8384)::(idx,uu____8386)::(s,uu____8388)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____8480 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____8480
               (fun nm1  ->
                  let uu____8493 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____8493
                    (fun idx1  ->
                       let uu____8502 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____8502
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _8537  ->
                                 FStar_Pervasives_Native.Some _8537)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____8538 ->
             (if w
              then
                (let uu____8557 =
                   let uu____8563 =
                     let uu____8565 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____8565
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____8563)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____8557)
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
        let uu____8621 =
          let uu____8626 =
            let uu____8627 =
              let uu____8640 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____8640  in
            let uu____8653 =
              let uu____8668 =
                let uu____8681 =
                  let uu____8690 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____8690 rng md  in
                FStar_Syntax_Syntax.as_arg uu____8681  in
              [uu____8668]  in
            uu____8627 :: uu____8653  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____8626
           in
        uu____8621 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____8774 =
          let uu____8779 =
            let uu____8780 =
              let uu____8793 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____8793  in
            let uu____8806 =
              let uu____8821 =
                let uu____8834 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____8834  in
              [uu____8821]  in
            uu____8780 :: uu____8806  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____8779
           in
        uu____8774 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___591_8883 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___591_8883.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___591_8883.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____8926 = FStar_Syntax_Util.head_and_args t1  in
    match uu____8926 with
    | (hd1,args) ->
        let uu____8995 =
          let uu____9012 =
            let uu____9013 = FStar_Syntax_Util.un_uinst hd1  in
            uu____9013.FStar_Syntax_Syntax.n  in
          (uu____9012, args)  in
        (match uu____8995 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____9040)::(md,uu____9042)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____9112 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____9112
               (fun t3  ->
                  let uu____9134 =
                    let uu____9143 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____9143 md  in
                  FStar_Util.bind_opt uu____9134
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _9178  -> FStar_Pervasives_Native.Some _9178)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____9191)::(post,uu____9193)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____9263 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____9263
               (fun pre1  ->
                  let uu____9285 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____9285
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _9308  -> FStar_Pervasives_Native.Some _9308)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _9345  -> FStar_Pervasives_Native.Some _9345)
               FStar_Reflection_Data.C_Unknown
         | uu____9346 ->
             (if w
              then
                (let uu____9365 =
                   let uu____9371 =
                     let uu____9373 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____9373
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____9371)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____9365)
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
    let uu___638_9418 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___638_9418.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___638_9418.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____9463 = FStar_Syntax_Util.head_and_args t1  in
    match uu____9463 with
    | (hd1,args) ->
        let uu____9532 =
          let uu____9551 =
            let uu____9552 = FStar_Syntax_Util.un_uinst hd1  in
            uu____9552.FStar_Syntax_Syntax.n  in
          (uu____9551, args)  in
        (match uu____9532 with
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
         | uu____9669 ->
             (if w
              then
                (let uu____9690 =
                   let uu____9696 =
                     let uu____9698 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____9698
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____9696)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____9690)
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
    let uu____9781 =
      let uu____9782 = FStar_Syntax_Subst.compress t  in
      uu____9782.FStar_Syntax_Syntax.n  in
    match uu____9781 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____9801;
          FStar_Syntax_Syntax.rng = uu____9802;_}
        ->
        let uu____9809 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____9809
    | uu____9830 ->
        (if w
         then
           (let uu____9833 =
              let uu____9839 =
                let uu____9841 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____9841
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____9839)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____9833)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____9901 uu____9902 =
    let uu____9910 =
      let uu____9916 = FStar_Ident.range_of_id i  in
      let uu____9917 = FStar_Ident.text_of_id i  in (uu____9916, uu____9917)
       in
    embed repr rng uu____9910  in
  let unembed_ident t w uu____9950 =
    let uu____9961 = unembed' w repr t  in
    match uu____9961 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____9987 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____9987
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____10002 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____10002
  
let (e_univ_name :
  FStar_Syntax_Syntax.univ_name FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.set_type FStar_Reflection_Data.fstar_refl_univ_name
    e_ident
  
let (e_univ_names :
  FStar_Syntax_Syntax.univ_name Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_univ_name 
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,univs1,ty,t) ->
        let uu____10085 =
          let uu____10090 =
            let uu____10091 =
              let uu____10104 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____10104  in
            let uu____10114 =
              let uu____10129 =
                let uu____10142 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____10142  in
              let uu____10154 =
                let uu____10169 =
                  let uu____10182 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____10182  in
                let uu____10195 =
                  let uu____10210 =
                    let uu____10223 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____10223  in
                  let uu____10236 =
                    let uu____10251 =
                      let uu____10264 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____10264  in
                    [uu____10251]  in
                  uu____10210 :: uu____10236  in
                uu____10169 :: uu____10195  in
              uu____10129 :: uu____10154  in
            uu____10091 :: uu____10114  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____10090
           in
        uu____10085 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____10359 =
          let uu____10364 =
            let uu____10365 =
              let uu____10378 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____10378  in
            let uu____10390 =
              let uu____10405 =
                let uu____10418 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____10418  in
              [uu____10405]  in
            uu____10365 :: uu____10390  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____10364
           in
        uu____10359 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____10496 =
          let uu____10501 =
            let uu____10502 =
              let uu____10515 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____10515  in
            let uu____10527 =
              let uu____10542 =
                let uu____10555 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____10555  in
              let uu____10568 =
                let uu____10583 =
                  let uu____10596 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____10596  in
                let uu____10605 =
                  let uu____10620 =
                    let uu____10633 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____10633  in
                  let uu____10646 =
                    let uu____10661 =
                      let uu____10674 =
                        let uu____10683 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____10683 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____10674  in
                    [uu____10661]  in
                  uu____10620 :: uu____10646  in
                uu____10583 :: uu____10605  in
              uu____10542 :: uu____10568  in
            uu____10502 :: uu____10527  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____10501
           in
        uu____10496 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___714_10771 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___714_10771.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___714_10771.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____10814 = FStar_Syntax_Util.head_and_args t1  in
    match uu____10814 with
    | (hd1,args) ->
        let uu____10883 =
          let uu____10900 =
            let uu____10901 = FStar_Syntax_Util.un_uinst hd1  in
            uu____10901.FStar_Syntax_Syntax.n  in
          (uu____10900, args)  in
        (match uu____10883 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____10928)::(us,uu____10930)::(bs,uu____10932)::
            (t2,uu____10934)::(dcs,uu____10936)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____11072 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____11072
               (fun nm1  ->
                  let uu____11090 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____11090
                    (fun us1  ->
                       let uu____11112 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____11112
                         (fun bs1  ->
                            let uu____11118 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____11118
                              (fun t3  ->
                                 let uu____11140 =
                                   let uu____11148 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____11148 dcs  in
                                 FStar_Util.bind_opt uu____11140
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _11178  ->
                                           FStar_Pervasives_Native.Some
                                             _11178)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____11193)::(fvar1,uu____11195)::(univs1,uu____11197)::
            (ty,uu____11199)::(t2,uu____11201)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____11337 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____11337
               (fun r1  ->
                  let uu____11347 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____11347
                    (fun fvar2  ->
                       let uu____11365 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____11365
                         (fun univs2  ->
                            let uu____11387 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____11387
                              (fun ty1  ->
                                 let uu____11409 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____11409
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _11432  ->
                                           FStar_Pervasives_Native.Some
                                             _11432)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____11475 ->
             (if w
              then
                (let uu____11494 =
                   let uu____11500 =
                     let uu____11502 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____11502
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____11500)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____11494)
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
          let uu____11548 =
            let uu____11553 =
              let uu____11554 =
                let uu____11567 =
                  let uu____11576 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____11576  in
                FStar_Syntax_Syntax.as_arg uu____11567  in
              [uu____11554]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____11553
             in
          uu____11548 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____11604 =
            let uu____11609 =
              let uu____11610 =
                let uu____11623 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____11623  in
              let uu____11632 =
                let uu____11647 =
                  let uu____11660 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____11660  in
                [uu____11647]  in
              uu____11610 :: uu____11632  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____11609
             in
          uu____11604 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___789_11705 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___789_11705.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___789_11705.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____11750 = FStar_Syntax_Util.head_and_args t1  in
    match uu____11750 with
    | (hd1,args) ->
        let uu____11819 =
          let uu____11836 =
            let uu____11837 = FStar_Syntax_Util.un_uinst hd1  in
            uu____11837.FStar_Syntax_Syntax.n  in
          (uu____11836, args)  in
        (match uu____11819 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____11890)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____11938 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____11938
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _11945  -> FStar_Pervasives_Native.Some _11945)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____11948)::(e2,uu____11950)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____12020 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____12020
               (fun e11  ->
                  let uu____12026 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____12026
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _12033  -> FStar_Pervasives_Native.Some _12033)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____12034 ->
             (if w
              then
                (let uu____12053 =
                   let uu____12059 =
                     let uu____12061 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____12061
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____12059)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____12053)
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
    let uu____12133 =
      let uu____12138 =
        let uu____12139 =
          let uu____12152 =
            let uu____12161 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____12161  in
          FStar_Syntax_Syntax.as_arg uu____12152  in
        [uu____12139]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____12138
       in
    uu____12133 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____12218 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____12218 with
    | (bv,aq) ->
        let uu____12244 =
          let uu____12249 =
            let uu____12250 =
              let uu____12263 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____12263  in
            let uu____12277 =
              let uu____12292 =
                let uu____12305 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____12305  in
              [uu____12292]  in
            uu____12250 :: uu____12277  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____12249
           in
        uu____12244 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____12382 =
      let uu____12387 =
        let uu____12388 =
          let uu____12401 =
            let uu____12410 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____12417 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____12410 i.FStar_Syntax_Syntax.rng uu____12417  in
          FStar_Syntax_Syntax.as_arg uu____12401  in
        [uu____12388]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____12387
       in
    uu____12382 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____12483 =
      let uu____12488 =
        let uu____12489 =
          let uu____12502 =
            let uu____12511 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____12511  in
          FStar_Syntax_Syntax.as_arg uu____12502  in
        [uu____12489]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____12488
       in
    uu____12483 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____12596 =
      let uu____12601 =
        let uu____12602 =
          let uu____12615 =
            let uu____12624 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____12624  in
          FStar_Syntax_Syntax.as_arg uu____12615  in
        [uu____12602]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____12601
       in
    uu____12596 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  