open Prims
let mk_emb :
  'Auu____64172 .
    (FStar_Range.range -> 'Auu____64172 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____64172 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____64172 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____64216 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____64216
  
let embed :
  'Auu____64264 .
    'Auu____64264 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____64264 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____64284 = FStar_Syntax_Embeddings.embed e x  in
        uu____64284 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____64325 .
    Prims.bool ->
      'Auu____64325 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____64325 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____64349 = FStar_Syntax_Embeddings.unembed e x  in
        uu____64349 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____64391 =
      let uu____64392 = FStar_Syntax_Subst.compress t  in
      uu____64392.FStar_Syntax_Syntax.n  in
    match uu____64391 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____64398;
          FStar_Syntax_Syntax.rng = uu____64399;_}
        ->
        let uu____64402 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64402
    | uu____64403 ->
        (if w
         then
           (let uu____64406 =
              let uu____64412 =
                let uu____64414 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____64414  in
              (FStar_Errors.Warning_NotEmbedded, uu____64412)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64406)
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
    let uu____64451 =
      let uu____64452 = FStar_Syntax_Subst.compress t  in
      uu____64452.FStar_Syntax_Syntax.n  in
    match uu____64451 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____64458;
          FStar_Syntax_Syntax.rng = uu____64459;_}
        ->
        let uu____64462 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64462
    | uu____64463 ->
        (if w
         then
           (let uu____64466 =
              let uu____64472 =
                let uu____64474 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____64474
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64472)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64466)
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
          let uu____64526 = f x  in
          FStar_Util.bind_opt uu____64526
            (fun x1  ->
               let uu____64534 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64534
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
        let uu____64603 =
          mapM_opt
            (fun uu____64616  ->
               match uu____64616 with
               | (bv,e) ->
                   let uu____64625 = unembed_term w e  in
                   FStar_Util.bind_opt uu____64625
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____64603
          (fun s  ->
             let uu____64639 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____64639)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____64641 =
        let uu____64642 = FStar_Syntax_Subst.compress t1  in
        uu____64642.FStar_Syntax_Syntax.n  in
      match uu____64641 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____64653 ->
          (if w
           then
             (let uu____64656 =
                let uu____64662 =
                  let uu____64664 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____64664
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____64662)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____64656)
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
          let uu____64699 =
            let uu____64704 =
              let uu____64705 =
                let uu____64714 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____64714  in
              [uu____64705]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____64704
             in
          uu____64699 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_64733 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_64733.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_64733.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64754 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64754 with
    | (hd1,args) ->
        let uu____64799 =
          let uu____64814 =
            let uu____64815 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64815.FStar_Syntax_Syntax.n  in
          (uu____64814, args)  in
        (match uu____64799 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____64870)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____64905 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____64905
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____64910 ->
             (if w
              then
                (let uu____64927 =
                   let uu____64933 =
                     let uu____64935 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____64935
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64933)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64927)
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
    let uu____64975 =
      let uu____64976 = FStar_Syntax_Subst.compress t  in
      uu____64976.FStar_Syntax_Syntax.n  in
    match uu____64975 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____64982;
          FStar_Syntax_Syntax.rng = uu____64983;_}
        ->
        let uu____64986 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64986
    | uu____64987 ->
        (if w
         then
           (let uu____64990 =
              let uu____64996 =
                let uu____64998 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____64998  in
              (FStar_Errors.Warning_NotEmbedded, uu____64996)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64990)
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
    let uu____65035 =
      let uu____65036 = FStar_Syntax_Subst.compress t  in
      uu____65036.FStar_Syntax_Syntax.n  in
    match uu____65035 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____65042;
          FStar_Syntax_Syntax.rng = uu____65043;_}
        ->
        let uu____65046 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65046
    | uu____65047 ->
        (if w
         then
           (let uu____65050 =
              let uu____65056 =
                let uu____65058 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____65058  in
              (FStar_Errors.Warning_NotEmbedded, uu____65056)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65050)
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
    let uu____65095 =
      let uu____65096 = FStar_Syntax_Subst.compress t  in
      uu____65096.FStar_Syntax_Syntax.n  in
    match uu____65095 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____65102;
          FStar_Syntax_Syntax.rng = uu____65103;_}
        ->
        let uu____65106 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65106
    | uu____65107 ->
        (if w
         then
           (let uu____65110 =
              let uu____65116 =
                let uu____65118 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____65118  in
              (FStar_Errors.Warning_NotEmbedded, uu____65116)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65110)
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
          let uu____65144 =
            let uu____65149 =
              let uu____65150 =
                let uu____65159 =
                  let uu____65160 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65160  in
                FStar_Syntax_Syntax.as_arg uu____65159  in
              [uu____65150]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____65149
             in
          uu____65144 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____65182 =
            let uu____65187 =
              let uu____65188 =
                let uu____65197 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____65197  in
              [uu____65188]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____65187
             in
          uu____65182 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____65218 =
            let uu____65223 =
              let uu____65224 =
                let uu____65233 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____65233  in
              [uu____65224]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____65223
             in
          uu____65218 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____65253 =
            let uu____65258 =
              let uu____65259 =
                let uu____65268 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____65268  in
              [uu____65259]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____65258
             in
          uu____65253 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_65290 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_65290.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_65290.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65311 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65311 with
    | (hd1,args) ->
        let uu____65356 =
          let uu____65371 =
            let uu____65372 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65372.FStar_Syntax_Syntax.n  in
          (uu____65371, args)  in
        (match uu____65356 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65446)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____65481 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65481
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65488  -> FStar_Pervasives_Native.Some _65488)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____65491)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____65526 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____65526
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _65537  -> FStar_Pervasives_Native.Some _65537)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____65540)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____65575 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____65575
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _65582  -> FStar_Pervasives_Native.Some _65582)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _65604  -> FStar_Pervasives_Native.Some _65604)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____65607)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____65642 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____65642
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _65661  -> FStar_Pervasives_Native.Some _65661)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____65662 ->
             (if w
              then
                (let uu____65679 =
                   let uu____65685 =
                     let uu____65687 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____65687
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65685)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65679)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____65700  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65713 =
            let uu____65718 =
              let uu____65719 =
                let uu____65728 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____65728  in
              [uu____65719]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____65718
             in
          uu____65713 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65753 =
            let uu____65758 =
              let uu____65759 =
                let uu____65768 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____65768  in
              let uu____65769 =
                let uu____65780 =
                  let uu____65789 =
                    let uu____65790 =
                      let uu____65795 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____65795  in
                    embed uu____65790 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____65789  in
                [uu____65780]  in
              uu____65759 :: uu____65769  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____65758
             in
          uu____65753 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65827 =
            let uu____65832 =
              let uu____65833 =
                let uu____65842 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65842  in
              [uu____65833]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____65832
             in
          uu____65827 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65862 =
            let uu____65867 =
              let uu____65868 =
                let uu____65877 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65877  in
              [uu____65868]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____65867
             in
          uu____65862 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65898 =
            let uu____65903 =
              let uu____65904 =
                let uu____65913 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65913  in
              let uu____65914 =
                let uu____65925 =
                  let uu____65934 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____65934  in
                [uu____65925]  in
              uu____65904 :: uu____65914  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____65903
             in
          uu____65898 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____65979 = FStar_Syntax_Util.head_and_args t1  in
      match uu____65979 with
      | (hd1,args) ->
          let uu____66024 =
            let uu____66037 =
              let uu____66038 = FStar_Syntax_Util.un_uinst hd1  in
              uu____66038.FStar_Syntax_Syntax.n  in
            (uu____66037, args)  in
          (match uu____66024 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____66053)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____66078 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____66078
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _66085  -> FStar_Pervasives_Native.Some _66085)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____66088)::(ps,uu____66090)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____66125 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____66125
                 (fun f1  ->
                    let uu____66131 =
                      let uu____66136 =
                        let uu____66141 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____66141  in
                      unembed' w uu____66136 ps  in
                    FStar_Util.bind_opt uu____66131
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _66154  ->
                              FStar_Pervasives_Native.Some _66154)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66159)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____66184 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66184
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66191  -> FStar_Pervasives_Native.Some _66191)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66194)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____66219 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66219
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66226  -> FStar_Pervasives_Native.Some _66226)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____66229)::(t2,uu____66231)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____66266 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66266
                 (fun bv1  ->
                    let uu____66272 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____66272
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _66279  ->
                              FStar_Pervasives_Native.Some _66279)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____66280 ->
               (if w
                then
                  (let uu____66295 =
                     let uu____66301 =
                       let uu____66303 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____66303
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____66301)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____66295)
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
    let uu____66330 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____66330
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____66345 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____66345 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____66368 =
            let uu____66373 =
              let uu____66374 =
                let uu____66383 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66383  in
              [uu____66374]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____66373
             in
          uu____66368 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____66403 =
            let uu____66408 =
              let uu____66409 =
                let uu____66418 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66418  in
              [uu____66409]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____66408
             in
          uu____66403 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____66438 =
            let uu____66443 =
              let uu____66444 =
                let uu____66453 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66453  in
              [uu____66444]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____66443
             in
          uu____66438 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66474 =
            let uu____66479 =
              let uu____66480 =
                let uu____66489 =
                  let uu____66490 = e_term_aq aq  in
                  embed uu____66490 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____66489  in
              let uu____66493 =
                let uu____66504 =
                  let uu____66513 =
                    let uu____66514 = e_argv_aq aq  in
                    embed uu____66514 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____66513  in
                [uu____66504]  in
              uu____66480 :: uu____66493  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____66479
             in
          uu____66474 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____66553 =
            let uu____66558 =
              let uu____66559 =
                let uu____66568 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66568  in
              let uu____66569 =
                let uu____66580 =
                  let uu____66589 =
                    let uu____66590 = e_term_aq aq  in
                    embed uu____66590 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66589  in
                [uu____66580]  in
              uu____66559 :: uu____66569  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____66558
             in
          uu____66553 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66621 =
            let uu____66626 =
              let uu____66627 =
                let uu____66636 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66636  in
              let uu____66637 =
                let uu____66648 =
                  let uu____66657 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____66657  in
                [uu____66648]  in
              uu____66627 :: uu____66637  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____66626
             in
          uu____66621 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66685 =
            let uu____66690 =
              let uu____66691 =
                let uu____66700 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____66700  in
              [uu____66691]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____66690
             in
          uu____66685 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____66721 =
            let uu____66726 =
              let uu____66727 =
                let uu____66736 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66736  in
              let uu____66737 =
                let uu____66748 =
                  let uu____66757 =
                    let uu____66758 = e_term_aq aq  in
                    embed uu____66758 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66757  in
                [uu____66748]  in
              uu____66727 :: uu____66737  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____66726
             in
          uu____66721 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66788 =
            let uu____66793 =
              let uu____66794 =
                let uu____66803 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____66803  in
              [uu____66794]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____66793
             in
          uu____66788 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66824 =
            let uu____66829 =
              let uu____66830 =
                let uu____66839 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____66839  in
              let uu____66840 =
                let uu____66851 =
                  let uu____66860 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____66860  in
                [uu____66851]  in
              uu____66830 :: uu____66840  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____66829
             in
          uu____66824 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66897 =
            let uu____66902 =
              let uu____66903 =
                let uu____66912 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____66912  in
              let uu____66914 =
                let uu____66925 =
                  let uu____66934 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____66934  in
                let uu____66935 =
                  let uu____66946 =
                    let uu____66955 =
                      let uu____66956 = e_term_aq aq  in
                      embed uu____66956 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____66955  in
                  let uu____66959 =
                    let uu____66970 =
                      let uu____66979 =
                        let uu____66980 = e_term_aq aq  in
                        embed uu____66980 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____66979  in
                    [uu____66970]  in
                  uu____66946 :: uu____66959  in
                uu____66925 :: uu____66935  in
              uu____66903 :: uu____66914  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____66902
             in
          uu____66897 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____67031 =
            let uu____67036 =
              let uu____67037 =
                let uu____67046 =
                  let uu____67047 = e_term_aq aq  in embed uu____67047 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____67046  in
              let uu____67050 =
                let uu____67061 =
                  let uu____67070 =
                    let uu____67071 =
                      let uu____67080 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____67080  in
                    embed uu____67071 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____67070  in
                [uu____67061]  in
              uu____67037 :: uu____67050  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____67036
             in
          uu____67031 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____67130 =
            let uu____67135 =
              let uu____67136 =
                let uu____67145 =
                  let uu____67146 = e_term_aq aq  in embed uu____67146 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67145  in
              let uu____67149 =
                let uu____67160 =
                  let uu____67169 =
                    let uu____67170 = e_term_aq aq  in
                    embed uu____67170 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____67169  in
                let uu____67173 =
                  let uu____67184 =
                    let uu____67193 =
                      let uu____67194 =
                        let uu____67199 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67199  in
                      embed uu____67194 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67193  in
                  [uu____67184]  in
                uu____67160 :: uu____67173  in
              uu____67136 :: uu____67149  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____67135
             in
          uu____67130 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____67245 =
            let uu____67250 =
              let uu____67251 =
                let uu____67260 =
                  let uu____67261 = e_term_aq aq  in embed uu____67261 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67260  in
              let uu____67264 =
                let uu____67275 =
                  let uu____67284 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____67284  in
                let uu____67285 =
                  let uu____67296 =
                    let uu____67305 =
                      let uu____67306 =
                        let uu____67311 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67311  in
                      embed uu____67306 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67305  in
                  [uu____67296]  in
                uu____67275 :: uu____67285  in
              uu____67251 :: uu____67264  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____67250
             in
          uu____67245 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_67350 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_67350.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_67350.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____67368 = FStar_Syntax_Util.head_and_args t  in
      match uu____67368 with
      | (hd1,args) ->
          let uu____67413 =
            let uu____67426 =
              let uu____67427 = FStar_Syntax_Util.un_uinst hd1  in
              uu____67427.FStar_Syntax_Syntax.n  in
            (uu____67426, args)  in
          (match uu____67413 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67442)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____67467 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67467
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67474  -> FStar_Pervasives_Native.Some _67474)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67477)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____67502 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67502
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67509  -> FStar_Pervasives_Native.Some _67509)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____67512)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____67537 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____67537
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _67544  -> FStar_Pervasives_Native.Some _67544)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____67547)::(r,uu____67549)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____67584 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____67584
                 (fun l1  ->
                    let uu____67590 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____67590
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _67597  ->
                              FStar_Pervasives_Native.Some _67597)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67600)::(t1,uu____67602)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____67637 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67637
                 (fun b1  ->
                    let uu____67643 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67643
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67650  ->
                              FStar_Pervasives_Native.Some _67650)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67653)::(t1,uu____67655)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____67690 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67690
                 (fun b1  ->
                    let uu____67696 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____67696
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _67703  ->
                              FStar_Pervasives_Native.Some _67703)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____67706)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____67731 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____67731
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _67738  -> FStar_Pervasives_Native.Some _67738)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67741)::(t1,uu____67743)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____67778 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67778
                 (fun b1  ->
                    let uu____67784 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67784
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67791  ->
                              FStar_Pervasives_Native.Some _67791)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____67794)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____67819 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____67819
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _67826  -> FStar_Pervasives_Native.Some _67826)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____67829)::(l,uu____67831)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____67866 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____67866
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _67875  -> FStar_Pervasives_Native.Some _67875)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____67878)::(b,uu____67880)::(t1,uu____67882)::
              (t2,uu____67884)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____67939 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____67939
                 (fun r1  ->
                    let uu____67949 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____67949
                      (fun b1  ->
                         let uu____67955 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____67955
                           (fun t11  ->
                              let uu____67961 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____67961
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _67968  ->
                                        FStar_Pervasives_Native.Some _67968)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____67972)::(brs,uu____67974)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____68009 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____68009
                 (fun t2  ->
                    let uu____68015 =
                      let uu____68020 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____68020 brs  in
                    FStar_Util.bind_opt uu____68015
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _68035  ->
                              FStar_Pervasives_Native.Some _68035)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68040)::(t1,uu____68042)::(tacopt,uu____68044)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____68089 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68089
                 (fun e1  ->
                    let uu____68095 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____68095
                      (fun t2  ->
                         let uu____68101 =
                           let uu____68106 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68106 tacopt  in
                         FStar_Util.bind_opt uu____68101
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68121  ->
                                   FStar_Pervasives_Native.Some _68121)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68126)::(c,uu____68128)::(tacopt,uu____68130)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____68175 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68175
                 (fun e1  ->
                    let uu____68181 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____68181
                      (fun c1  ->
                         let uu____68187 =
                           let uu____68192 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68192 tacopt  in
                         FStar_Util.bind_opt uu____68187
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68207  ->
                                   FStar_Pervasives_Native.Some _68207)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _68227  -> FStar_Pervasives_Native.Some _68227)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____68228 ->
               (if w
                then
                  (let uu____68243 =
                     let uu____68249 =
                       let uu____68251 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____68251
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____68249)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____68243)
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
    let uu____68280 =
      let uu____68285 =
        let uu____68286 =
          let uu____68295 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____68295  in
        let uu____68297 =
          let uu____68308 =
            let uu____68317 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____68317  in
          let uu____68318 =
            let uu____68329 =
              let uu____68338 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____68338  in
            [uu____68329]  in
          uu____68308 :: uu____68318  in
        uu____68286 :: uu____68297  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____68285
       in
    uu____68280 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68391 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68391 with
    | (hd1,args) ->
        let uu____68436 =
          let uu____68449 =
            let uu____68450 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68450.FStar_Syntax_Syntax.n  in
          (uu____68449, args)  in
        (match uu____68436 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____68465)::(idx,uu____68467)::(s,uu____68469)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____68514 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____68514
               (fun nm1  ->
                  let uu____68524 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____68524
                    (fun idx1  ->
                       let uu____68530 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____68530
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _68537  ->
                                 FStar_Pervasives_Native.Some _68537)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____68538 ->
             (if w
              then
                (let uu____68553 =
                   let uu____68559 =
                     let uu____68561 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____68561
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____68559)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____68553)
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
        let uu____68587 =
          let uu____68592 =
            let uu____68593 =
              let uu____68602 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____68602  in
            let uu____68603 =
              let uu____68614 =
                let uu____68623 =
                  let uu____68624 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____68624 rng md  in
                FStar_Syntax_Syntax.as_arg uu____68623  in
              [uu____68614]  in
            uu____68593 :: uu____68603  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____68592
           in
        uu____68587 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____68662 =
          let uu____68667 =
            let uu____68668 =
              let uu____68677 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____68677  in
            let uu____68678 =
              let uu____68689 =
                let uu____68698 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____68698  in
              [uu____68689]  in
            uu____68668 :: uu____68678  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____68667
           in
        uu____68662 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_68725 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_68725.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_68725.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68744 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68744 with
    | (hd1,args) ->
        let uu____68789 =
          let uu____68802 =
            let uu____68803 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68803.FStar_Syntax_Syntax.n  in
          (uu____68802, args)  in
        (match uu____68789 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____68818)::(md,uu____68820)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____68855 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____68855
               (fun t3  ->
                  let uu____68861 =
                    let uu____68866 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____68866 md  in
                  FStar_Util.bind_opt uu____68861
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _68881  -> FStar_Pervasives_Native.Some _68881)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____68886)::(post,uu____68888)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____68923 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____68923
               (fun pre1  ->
                  let uu____68929 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____68929
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _68936  -> FStar_Pervasives_Native.Some _68936)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _68954  -> FStar_Pervasives_Native.Some _68954)
               FStar_Reflection_Data.C_Unknown
         | uu____68955 ->
             (if w
              then
                (let uu____68970 =
                   let uu____68976 =
                     let uu____68978 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____68978
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____68976)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____68970)
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
    let uu___1175_69003 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_69003.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_69003.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69024 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69024 with
    | (hd1,args) ->
        let uu____69069 =
          let uu____69084 =
            let uu____69085 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69085.FStar_Syntax_Syntax.n  in
          (uu____69084, args)  in
        (match uu____69069 with
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
         | uu____69157 ->
             (if w
              then
                (let uu____69174 =
                   let uu____69180 =
                     let uu____69182 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____69182
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69180)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69174)
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
    let uu____69219 =
      let uu____69220 = FStar_Syntax_Subst.compress t  in
      uu____69220.FStar_Syntax_Syntax.n  in
    match uu____69219 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____69226;
          FStar_Syntax_Syntax.rng = uu____69227;_}
        ->
        let uu____69230 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____69230
    | uu____69231 ->
        (if w
         then
           (let uu____69234 =
              let uu____69240 =
                let uu____69242 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____69242
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____69240)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69234)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____69302 uu____69303 =
    let uu____69325 =
      let uu____69331 = FStar_Ident.range_of_id i  in
      let uu____69332 = FStar_Ident.text_of_id i  in
      (uu____69331, uu____69332)  in
    embed repr rng uu____69325  in
  let unembed_ident t w uu____69360 =
    let uu____69366 = unembed' w repr t  in
    match uu____69366 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____69390 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____69390
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____69397 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____69397
  
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
        let uu____69436 =
          let uu____69441 =
            let uu____69442 =
              let uu____69451 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____69451  in
            let uu____69453 =
              let uu____69464 =
                let uu____69473 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____69473  in
              let uu____69474 =
                let uu____69485 =
                  let uu____69494 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____69494  in
                let uu____69497 =
                  let uu____69508 =
                    let uu____69517 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____69517  in
                  let uu____69518 =
                    let uu____69529 =
                      let uu____69538 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____69538  in
                    [uu____69529]  in
                  uu____69508 :: uu____69518  in
                uu____69485 :: uu____69497  in
              uu____69464 :: uu____69474  in
            uu____69442 :: uu____69453  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____69441
           in
        uu____69436 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____69591 =
          let uu____69596 =
            let uu____69597 =
              let uu____69606 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69606  in
            let uu____69610 =
              let uu____69621 =
                let uu____69630 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____69630  in
              [uu____69621]  in
            uu____69597 :: uu____69610  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____69596
           in
        uu____69591 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____69674 =
          let uu____69679 =
            let uu____69680 =
              let uu____69689 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69689  in
            let uu____69693 =
              let uu____69704 =
                let uu____69713 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____69713  in
              let uu____69716 =
                let uu____69727 =
                  let uu____69736 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____69736  in
                let uu____69737 =
                  let uu____69748 =
                    let uu____69757 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____69757  in
                  let uu____69758 =
                    let uu____69769 =
                      let uu____69778 =
                        let uu____69779 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____69779 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____69778  in
                    [uu____69769]  in
                  uu____69748 :: uu____69758  in
                uu____69727 :: uu____69737  in
              uu____69704 :: uu____69716  in
            uu____69680 :: uu____69693  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____69679
           in
        uu____69674 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_69845 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_69845.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_69845.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69864 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69864 with
    | (hd1,args) ->
        let uu____69909 =
          let uu____69922 =
            let uu____69923 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69923.FStar_Syntax_Syntax.n  in
          (uu____69922, args)  in
        (match uu____69909 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____69938)::(us,uu____69940)::(bs,uu____69942)::
            (t2,uu____69944)::(dcs,uu____69946)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____70011 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____70011
               (fun nm1  ->
                  let uu____70029 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____70029
                    (fun us1  ->
                       let uu____70043 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____70043
                         (fun bs1  ->
                            let uu____70049 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____70049
                              (fun t3  ->
                                 let uu____70055 =
                                   let uu____70063 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____70063 dcs  in
                                 FStar_Util.bind_opt uu____70055
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _70093  ->
                                           FStar_Pervasives_Native.Some
                                             _70093)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____70102)::(fvar1,uu____70104)::(univs1,uu____70106)::
            (ty,uu____70108)::(t2,uu____70110)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____70175 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____70175
               (fun r1  ->
                  let uu____70185 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____70185
                    (fun fvar2  ->
                       let uu____70191 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____70191
                         (fun univs2  ->
                            let uu____70205 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____70205
                              (fun ty1  ->
                                 let uu____70211 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____70211
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _70218  ->
                                           FStar_Pervasives_Native.Some
                                             _70218)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____70237 ->
             (if w
              then
                (let uu____70252 =
                   let uu____70258 =
                     let uu____70260 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____70260
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70258)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70252)
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
          let uu____70286 =
            let uu____70291 =
              let uu____70292 =
                let uu____70301 =
                  let uu____70302 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____70302  in
                FStar_Syntax_Syntax.as_arg uu____70301  in
              [uu____70292]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____70291
             in
          uu____70286 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____70324 =
            let uu____70329 =
              let uu____70330 =
                let uu____70339 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____70339  in
              let uu____70340 =
                let uu____70351 =
                  let uu____70360 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____70360  in
                [uu____70351]  in
              uu____70330 :: uu____70340  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____70329
             in
          uu____70324 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_70387 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_70387.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_70387.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____70408 = FStar_Syntax_Util.head_and_args t1  in
    match uu____70408 with
    | (hd1,args) ->
        let uu____70453 =
          let uu____70466 =
            let uu____70467 = FStar_Syntax_Util.un_uinst hd1  in
            uu____70467.FStar_Syntax_Syntax.n  in
          (uu____70466, args)  in
        (match uu____70453 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____70497)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____70522 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____70522
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _70529  -> FStar_Pervasives_Native.Some _70529)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____70532)::(e2,uu____70534)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____70569 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____70569
               (fun e11  ->
                  let uu____70575 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____70575
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _70582  -> FStar_Pervasives_Native.Some _70582)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____70583 ->
             (if w
              then
                (let uu____70598 =
                   let uu____70604 =
                     let uu____70606 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____70606
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70604)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70598)
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
    let uu____70630 =
      let uu____70635 =
        let uu____70636 =
          let uu____70645 =
            let uu____70646 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____70646  in
          FStar_Syntax_Syntax.as_arg uu____70645  in
        [uu____70636]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____70635
       in
    uu____70630 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70672 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____70672 with
    | (bv,aq) ->
        let uu____70679 =
          let uu____70684 =
            let uu____70685 =
              let uu____70694 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____70694  in
            let uu____70695 =
              let uu____70706 =
                let uu____70715 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____70715  in
              [uu____70706]  in
            uu____70685 :: uu____70695  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____70684
           in
        uu____70679 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70749 =
      let uu____70754 =
        let uu____70755 =
          let uu____70764 =
            let uu____70765 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____70772 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____70765 i.FStar_Syntax_Syntax.rng uu____70772  in
          FStar_Syntax_Syntax.as_arg uu____70764  in
        [uu____70755]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____70754
       in
    uu____70749 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70804 =
      let uu____70809 =
        let uu____70810 =
          let uu____70819 =
            let uu____70820 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____70820  in
          FStar_Syntax_Syntax.as_arg uu____70819  in
        [uu____70810]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____70809
       in
    uu____70804 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70852 =
      let uu____70857 =
        let uu____70858 =
          let uu____70867 =
            let uu____70868 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____70868  in
          FStar_Syntax_Syntax.as_arg uu____70867  in
        [uu____70858]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____70857
       in
    uu____70852 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  