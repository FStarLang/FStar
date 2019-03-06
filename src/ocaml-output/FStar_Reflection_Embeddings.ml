open Prims
let mk_emb :
  'Auu____60151 .
    (FStar_Range.range -> 'Auu____60151 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____60151 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____60151 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____60195 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____60195
  
let embed :
  'Auu____60222 .
    'Auu____60222 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____60222 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____60242 = FStar_Syntax_Embeddings.embed e x  in
        uu____60242 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____60260 .
    Prims.bool ->
      'Auu____60260 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____60260 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____60284 = FStar_Syntax_Embeddings.unembed e x  in
        uu____60284 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____60322 =
      let uu____60323 = FStar_Syntax_Subst.compress t  in
      uu____60323.FStar_Syntax_Syntax.n  in
    match uu____60322 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____60329;
          FStar_Syntax_Syntax.rng = uu____60330;_}
        ->
        let uu____60333 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60333
    | uu____60334 ->
        (if w
         then
           (let uu____60337 =
              let uu____60343 =
                let uu____60345 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____60345  in
              (FStar_Errors.Warning_NotEmbedded, uu____60343)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60337)
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
    let uu____60382 =
      let uu____60383 = FStar_Syntax_Subst.compress t  in
      uu____60383.FStar_Syntax_Syntax.n  in
    match uu____60382 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____60389;
          FStar_Syntax_Syntax.rng = uu____60390;_}
        ->
        let uu____60393 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60393
    | uu____60394 ->
        (if w
         then
           (let uu____60397 =
              let uu____60403 =
                let uu____60405 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____60405
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____60403)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60397)
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
          let uu____60457 = f x  in
          FStar_Util.bind_opt uu____60457
            (fun x1  ->
               let uu____60465 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____60465
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
        let uu____60534 =
          mapM_opt
            (fun uu____60547  ->
               match uu____60547 with
               | (bv,e) ->
                   let uu____60556 = unembed_term w e  in
                   FStar_Util.bind_opt uu____60556
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____60534
          (fun s  ->
             let uu____60570 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____60570)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____60572 =
        let uu____60573 = FStar_Syntax_Subst.compress t1  in
        uu____60573.FStar_Syntax_Syntax.n  in
      match uu____60572 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____60584 ->
          (if w
           then
             (let uu____60587 =
                let uu____60593 =
                  let uu____60595 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____60595
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____60593)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____60587)
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
          let uu____60630 =
            let uu____60635 =
              let uu____60636 =
                let uu____60645 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____60645  in
              [uu____60636]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____60635
             in
          uu____60630 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_60662 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_60662.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_60662.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____60683 = FStar_Syntax_Util.head_and_args t1  in
    match uu____60683 with
    | (hd1,args) ->
        let uu____60728 =
          let uu____60743 =
            let uu____60744 = FStar_Syntax_Util.un_uinst hd1  in
            uu____60744.FStar_Syntax_Syntax.n  in
          (uu____60743, args)  in
        (match uu____60728 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____60799)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____60834 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____60834
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____60839 ->
             (if w
              then
                (let uu____60856 =
                   let uu____60862 =
                     let uu____60864 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____60864
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60862)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60856)
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
    let uu____60904 =
      let uu____60905 = FStar_Syntax_Subst.compress t  in
      uu____60905.FStar_Syntax_Syntax.n  in
    match uu____60904 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____60911;
          FStar_Syntax_Syntax.rng = uu____60912;_}
        ->
        let uu____60915 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60915
    | uu____60916 ->
        (if w
         then
           (let uu____60919 =
              let uu____60925 =
                let uu____60927 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____60927  in
              (FStar_Errors.Warning_NotEmbedded, uu____60925)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60919)
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
    let uu____60964 =
      let uu____60965 = FStar_Syntax_Subst.compress t  in
      uu____60965.FStar_Syntax_Syntax.n  in
    match uu____60964 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____60971;
          FStar_Syntax_Syntax.rng = uu____60972;_}
        ->
        let uu____60975 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60975
    | uu____60976 ->
        (if w
         then
           (let uu____60979 =
              let uu____60985 =
                let uu____60987 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____60987  in
              (FStar_Errors.Warning_NotEmbedded, uu____60985)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60979)
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
    let uu____61024 =
      let uu____61025 = FStar_Syntax_Subst.compress t  in
      uu____61025.FStar_Syntax_Syntax.n  in
    match uu____61024 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____61031;
          FStar_Syntax_Syntax.rng = uu____61032;_}
        ->
        let uu____61035 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____61035
    | uu____61036 ->
        (if w
         then
           (let uu____61039 =
              let uu____61045 =
                let uu____61047 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____61047  in
              (FStar_Errors.Warning_NotEmbedded, uu____61045)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____61039)
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
          let uu____61073 =
            let uu____61078 =
              let uu____61079 =
                let uu____61088 =
                  let uu____61089 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____61089  in
                FStar_Syntax_Syntax.as_arg uu____61088  in
              [uu____61079]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____61078
             in
          uu____61073 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____61109 =
            let uu____61114 =
              let uu____61115 =
                let uu____61124 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____61124  in
              [uu____61115]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____61114
             in
          uu____61109 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____61143 =
            let uu____61148 =
              let uu____61149 =
                let uu____61158 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____61158  in
              [uu____61149]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____61148
             in
          uu____61143 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____61176 =
            let uu____61181 =
              let uu____61182 =
                let uu____61191 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____61191  in
              [uu____61182]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____61181
             in
          uu____61176 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_61211 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_61211.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_61211.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____61232 = FStar_Syntax_Util.head_and_args t1  in
    match uu____61232 with
    | (hd1,args) ->
        let uu____61277 =
          let uu____61292 =
            let uu____61293 = FStar_Syntax_Util.un_uinst hd1  in
            uu____61293.FStar_Syntax_Syntax.n  in
          (uu____61292, args)  in
        (match uu____61277 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____61367)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____61402 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____61402
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _61409  -> FStar_Pervasives_Native.Some _61409)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____61412)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____61447 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____61447
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _61458  -> FStar_Pervasives_Native.Some _61458)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____61461)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____61496 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____61496
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _61503  -> FStar_Pervasives_Native.Some _61503)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _61525  -> FStar_Pervasives_Native.Some _61525)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____61528)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____61563 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____61563
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _61582  -> FStar_Pervasives_Native.Some _61582)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____61583 ->
             (if w
              then
                (let uu____61600 =
                   let uu____61606 =
                     let uu____61608 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____61608
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____61606)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____61600)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____61621  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____61634 =
            let uu____61639 =
              let uu____61640 =
                let uu____61649 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____61649  in
              [uu____61640]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____61639
             in
          uu____61634 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____61672 =
            let uu____61677 =
              let uu____61678 =
                let uu____61687 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61687  in
              let uu____61688 =
                let uu____61699 =
                  let uu____61708 =
                    let uu____61709 =
                      let uu____61714 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____61714  in
                    embed uu____61709 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____61708  in
                [uu____61699]  in
              uu____61678 :: uu____61688  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____61677
             in
          uu____61672 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____61744 =
            let uu____61749 =
              let uu____61750 =
                let uu____61759 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61759  in
              [uu____61750]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____61749
             in
          uu____61744 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____61777 =
            let uu____61782 =
              let uu____61783 =
                let uu____61792 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61792  in
              [uu____61783]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____61782
             in
          uu____61777 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____61811 =
            let uu____61816 =
              let uu____61817 =
                let uu____61826 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61826  in
              let uu____61827 =
                let uu____61838 =
                  let uu____61847 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____61847  in
                [uu____61838]  in
              uu____61817 :: uu____61827  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____61816
             in
          uu____61811 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____61890 = FStar_Syntax_Util.head_and_args t1  in
      match uu____61890 with
      | (hd1,args) ->
          let uu____61935 =
            let uu____61948 =
              let uu____61949 = FStar_Syntax_Util.un_uinst hd1  in
              uu____61949.FStar_Syntax_Syntax.n  in
            (uu____61948, args)  in
          (match uu____61935 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____61964)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____61989 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____61989
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _61996  -> FStar_Pervasives_Native.Some _61996)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____61999)::(ps,uu____62001)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____62036 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____62036
                 (fun f1  ->
                    let uu____62042 =
                      let uu____62047 =
                        let uu____62052 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____62052  in
                      unembed' w uu____62047 ps  in
                    FStar_Util.bind_opt uu____62042
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _62065  ->
                              FStar_Pervasives_Native.Some _62065)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____62070)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____62095 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____62095
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _62102  -> FStar_Pervasives_Native.Some _62102)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____62105)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____62130 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____62130
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _62137  -> FStar_Pervasives_Native.Some _62137)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____62140)::(t2,uu____62142)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____62177 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____62177
                 (fun bv1  ->
                    let uu____62183 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____62183
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _62190  ->
                              FStar_Pervasives_Native.Some _62190)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____62191 ->
               (if w
                then
                  (let uu____62206 =
                     let uu____62212 =
                       let uu____62214 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____62214
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____62212)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____62206)
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
    let uu____62241 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____62241
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____62256 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____62256 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____62279 =
            let uu____62284 =
              let uu____62285 =
                let uu____62294 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____62294  in
              [uu____62285]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____62284
             in
          uu____62279 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____62312 =
            let uu____62317 =
              let uu____62318 =
                let uu____62327 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____62327  in
              [uu____62318]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____62317
             in
          uu____62312 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____62345 =
            let uu____62350 =
              let uu____62351 =
                let uu____62360 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____62360  in
              [uu____62351]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____62350
             in
          uu____62345 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____62379 =
            let uu____62384 =
              let uu____62385 =
                let uu____62394 =
                  let uu____62395 = e_term_aq aq  in
                  embed uu____62395 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____62394  in
              let uu____62398 =
                let uu____62409 =
                  let uu____62418 =
                    let uu____62419 = e_argv_aq aq  in
                    embed uu____62419 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____62418  in
                [uu____62409]  in
              uu____62385 :: uu____62398  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____62384
             in
          uu____62379 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____62456 =
            let uu____62461 =
              let uu____62462 =
                let uu____62471 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____62471  in
              let uu____62472 =
                let uu____62483 =
                  let uu____62492 =
                    let uu____62493 = e_term_aq aq  in
                    embed uu____62493 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____62492  in
                [uu____62483]  in
              uu____62462 :: uu____62472  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____62461
             in
          uu____62456 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____62522 =
            let uu____62527 =
              let uu____62528 =
                let uu____62537 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____62537  in
              let uu____62538 =
                let uu____62549 =
                  let uu____62558 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____62558  in
                [uu____62549]  in
              uu____62528 :: uu____62538  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____62527
             in
          uu____62522 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____62584 =
            let uu____62589 =
              let uu____62590 =
                let uu____62599 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____62599  in
              [uu____62590]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____62589
             in
          uu____62584 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____62618 =
            let uu____62623 =
              let uu____62624 =
                let uu____62633 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____62633  in
              let uu____62634 =
                let uu____62645 =
                  let uu____62654 =
                    let uu____62655 = e_term_aq aq  in
                    embed uu____62655 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____62654  in
                [uu____62645]  in
              uu____62624 :: uu____62634  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____62623
             in
          uu____62618 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____62683 =
            let uu____62688 =
              let uu____62689 =
                let uu____62698 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____62698  in
              [uu____62689]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____62688
             in
          uu____62683 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____62717 =
            let uu____62722 =
              let uu____62723 =
                let uu____62732 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____62732  in
              let uu____62733 =
                let uu____62744 =
                  let uu____62753 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____62753  in
                [uu____62744]  in
              uu____62723 :: uu____62733  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____62722
             in
          uu____62717 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____62788 =
            let uu____62793 =
              let uu____62794 =
                let uu____62803 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____62803  in
              let uu____62805 =
                let uu____62816 =
                  let uu____62825 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____62825  in
                let uu____62826 =
                  let uu____62837 =
                    let uu____62846 =
                      let uu____62847 = e_term_aq aq  in
                      embed uu____62847 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____62846  in
                  let uu____62850 =
                    let uu____62861 =
                      let uu____62870 =
                        let uu____62871 = e_term_aq aq  in
                        embed uu____62871 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____62870  in
                    [uu____62861]  in
                  uu____62837 :: uu____62850  in
                uu____62816 :: uu____62826  in
              uu____62794 :: uu____62805  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____62793
             in
          uu____62788 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____62920 =
            let uu____62925 =
              let uu____62926 =
                let uu____62935 =
                  let uu____62936 = e_term_aq aq  in embed uu____62936 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____62935  in
              let uu____62939 =
                let uu____62950 =
                  let uu____62959 =
                    let uu____62960 =
                      let uu____62969 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____62969  in
                    embed uu____62960 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____62959  in
                [uu____62950]  in
              uu____62926 :: uu____62939  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____62925
             in
          uu____62920 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____63017 =
            let uu____63022 =
              let uu____63023 =
                let uu____63032 =
                  let uu____63033 = e_term_aq aq  in embed uu____63033 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____63032  in
              let uu____63036 =
                let uu____63047 =
                  let uu____63056 =
                    let uu____63057 = e_term_aq aq  in
                    embed uu____63057 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____63056  in
                let uu____63060 =
                  let uu____63071 =
                    let uu____63080 =
                      let uu____63081 =
                        let uu____63086 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____63086  in
                      embed uu____63081 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____63080  in
                  [uu____63071]  in
                uu____63047 :: uu____63060  in
              uu____63023 :: uu____63036  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____63022
             in
          uu____63017 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____63130 =
            let uu____63135 =
              let uu____63136 =
                let uu____63145 =
                  let uu____63146 = e_term_aq aq  in embed uu____63146 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____63145  in
              let uu____63149 =
                let uu____63160 =
                  let uu____63169 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____63169  in
                let uu____63170 =
                  let uu____63181 =
                    let uu____63190 =
                      let uu____63191 =
                        let uu____63196 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____63196  in
                      embed uu____63191 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____63190  in
                  [uu____63181]  in
                uu____63160 :: uu____63170  in
              uu____63136 :: uu____63149  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____63135
             in
          uu____63130 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_63233 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_63233.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_63233.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____63251 = FStar_Syntax_Util.head_and_args t  in
      match uu____63251 with
      | (hd1,args) ->
          let uu____63296 =
            let uu____63309 =
              let uu____63310 = FStar_Syntax_Util.un_uinst hd1  in
              uu____63310.FStar_Syntax_Syntax.n  in
            (uu____63309, args)  in
          (match uu____63296 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____63325)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____63350 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____63350
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _63357  -> FStar_Pervasives_Native.Some _63357)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____63360)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____63385 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____63385
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _63392  -> FStar_Pervasives_Native.Some _63392)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____63395)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____63420 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____63420
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _63427  -> FStar_Pervasives_Native.Some _63427)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____63430)::(r,uu____63432)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____63467 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____63467
                 (fun l1  ->
                    let uu____63473 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____63473
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _63480  ->
                              FStar_Pervasives_Native.Some _63480)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____63483)::(t1,uu____63485)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____63520 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____63520
                 (fun b1  ->
                    let uu____63526 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____63526
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _63533  ->
                              FStar_Pervasives_Native.Some _63533)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____63536)::(t1,uu____63538)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____63573 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____63573
                 (fun b1  ->
                    let uu____63579 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____63579
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _63586  ->
                              FStar_Pervasives_Native.Some _63586)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____63589)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____63614 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____63614
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _63621  -> FStar_Pervasives_Native.Some _63621)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____63624)::(t1,uu____63626)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____63661 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____63661
                 (fun b1  ->
                    let uu____63667 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____63667
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _63674  ->
                              FStar_Pervasives_Native.Some _63674)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____63677)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____63702 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____63702
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _63709  -> FStar_Pervasives_Native.Some _63709)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____63712)::(l,uu____63714)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____63749 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____63749
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _63758  -> FStar_Pervasives_Native.Some _63758)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____63761)::(b,uu____63763)::(t1,uu____63765)::
              (t2,uu____63767)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____63822 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____63822
                 (fun r1  ->
                    let uu____63832 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____63832
                      (fun b1  ->
                         let uu____63838 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____63838
                           (fun t11  ->
                              let uu____63844 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____63844
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _63851  ->
                                        FStar_Pervasives_Native.Some _63851)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____63855)::(brs,uu____63857)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____63892 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____63892
                 (fun t2  ->
                    let uu____63898 =
                      let uu____63903 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____63903 brs  in
                    FStar_Util.bind_opt uu____63898
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _63918  ->
                              FStar_Pervasives_Native.Some _63918)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63923)::(t1,uu____63925)::(tacopt,uu____63927)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____63972 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63972
                 (fun e1  ->
                    let uu____63978 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____63978
                      (fun t2  ->
                         let uu____63984 =
                           let uu____63989 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63989 tacopt  in
                         FStar_Util.bind_opt uu____63984
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _64004  ->
                                   FStar_Pervasives_Native.Some _64004)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____64009)::(c,uu____64011)::(tacopt,uu____64013)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____64058 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____64058
                 (fun e1  ->
                    let uu____64064 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____64064
                      (fun c1  ->
                         let uu____64070 =
                           let uu____64075 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____64075 tacopt  in
                         FStar_Util.bind_opt uu____64070
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _64090  ->
                                   FStar_Pervasives_Native.Some _64090)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _64110  -> FStar_Pervasives_Native.Some _64110)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____64111 ->
               (if w
                then
                  (let uu____64126 =
                     let uu____64132 =
                       let uu____64134 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____64134
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____64132)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____64126)
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
    let uu____64163 =
      let uu____64168 =
        let uu____64169 =
          let uu____64178 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____64178  in
        let uu____64180 =
          let uu____64191 =
            let uu____64200 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____64200  in
          let uu____64201 =
            let uu____64212 =
              let uu____64221 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____64221  in
            [uu____64212]  in
          uu____64191 :: uu____64201  in
        uu____64169 :: uu____64180  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____64168
       in
    uu____64163 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64272 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64272 with
    | (hd1,args) ->
        let uu____64317 =
          let uu____64330 =
            let uu____64331 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64331.FStar_Syntax_Syntax.n  in
          (uu____64330, args)  in
        (match uu____64317 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____64346)::(idx,uu____64348)::(s,uu____64350)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____64395 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____64395
               (fun nm1  ->
                  let uu____64405 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____64405
                    (fun idx1  ->
                       let uu____64411 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____64411
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _64418  ->
                                 FStar_Pervasives_Native.Some _64418)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____64419 ->
             (if w
              then
                (let uu____64434 =
                   let uu____64440 =
                     let uu____64442 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____64442
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64440)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64434)
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
        let uu____64468 =
          let uu____64473 =
            let uu____64474 =
              let uu____64483 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____64483  in
            let uu____64484 =
              let uu____64495 =
                let uu____64504 =
                  let uu____64505 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____64505 rng md  in
                FStar_Syntax_Syntax.as_arg uu____64504  in
              [uu____64495]  in
            uu____64474 :: uu____64484  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____64473
           in
        uu____64468 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____64541 =
          let uu____64546 =
            let uu____64547 =
              let uu____64556 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____64556  in
            let uu____64557 =
              let uu____64568 =
                let uu____64577 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____64577  in
              [uu____64568]  in
            uu____64547 :: uu____64557  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____64546
           in
        uu____64541 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_64602 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_64602.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_64602.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64621 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64621 with
    | (hd1,args) ->
        let uu____64666 =
          let uu____64679 =
            let uu____64680 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64680.FStar_Syntax_Syntax.n  in
          (uu____64679, args)  in
        (match uu____64666 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____64695)::(md,uu____64697)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____64732 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____64732
               (fun t3  ->
                  let uu____64738 =
                    let uu____64743 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____64743 md  in
                  FStar_Util.bind_opt uu____64738
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _64758  -> FStar_Pervasives_Native.Some _64758)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____64763)::(post,uu____64765)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____64800 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____64800
               (fun pre1  ->
                  let uu____64806 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____64806
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _64813  -> FStar_Pervasives_Native.Some _64813)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _64831  -> FStar_Pervasives_Native.Some _64831)
               FStar_Reflection_Data.C_Unknown
         | uu____64832 ->
             (if w
              then
                (let uu____64847 =
                   let uu____64853 =
                     let uu____64855 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____64855
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64853)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64847)
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
    let uu___1175_64880 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_64880.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_64880.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64901 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64901 with
    | (hd1,args) ->
        let uu____64946 =
          let uu____64961 =
            let uu____64962 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64962.FStar_Syntax_Syntax.n  in
          (uu____64961, args)  in
        (match uu____64946 with
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
         | uu____65034 ->
             (if w
              then
                (let uu____65051 =
                   let uu____65057 =
                     let uu____65059 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____65059
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65057)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65051)
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
    let uu____65096 =
      let uu____65097 = FStar_Syntax_Subst.compress t  in
      uu____65097.FStar_Syntax_Syntax.n  in
    match uu____65096 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____65103;
          FStar_Syntax_Syntax.rng = uu____65104;_}
        ->
        let uu____65107 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65107
    | uu____65108 ->
        (if w
         then
           (let uu____65111 =
              let uu____65117 =
                let uu____65119 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____65119
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65117)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65111)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____65159 uu____65160 =
    let uu____65162 =
      let uu____65168 = FStar_Ident.range_of_id i  in
      let uu____65169 = FStar_Ident.text_of_id i  in
      (uu____65168, uu____65169)  in
    embed repr rng uu____65162  in
  let unembed_ident t w uu____65196 =
    let uu____65201 = unembed' w repr t  in
    match uu____65201 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____65225 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____65225
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____65232 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____65232
  
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
        let uu____65271 =
          let uu____65276 =
            let uu____65277 =
              let uu____65286 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____65286  in
            let uu____65288 =
              let uu____65299 =
                let uu____65308 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____65308  in
              let uu____65309 =
                let uu____65320 =
                  let uu____65329 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____65329  in
                let uu____65332 =
                  let uu____65343 =
                    let uu____65352 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____65352  in
                  let uu____65353 =
                    let uu____65364 =
                      let uu____65373 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____65373  in
                    [uu____65364]  in
                  uu____65343 :: uu____65353  in
                uu____65320 :: uu____65332  in
              uu____65299 :: uu____65309  in
            uu____65277 :: uu____65288  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____65276
           in
        uu____65271 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____65424 =
          let uu____65429 =
            let uu____65430 =
              let uu____65439 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____65439  in
            let uu____65443 =
              let uu____65454 =
                let uu____65463 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____65463  in
              [uu____65454]  in
            uu____65430 :: uu____65443  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____65429
           in
        uu____65424 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____65505 =
          let uu____65510 =
            let uu____65511 =
              let uu____65520 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____65520  in
            let uu____65524 =
              let uu____65535 =
                let uu____65544 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____65544  in
              let uu____65547 =
                let uu____65558 =
                  let uu____65567 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____65567  in
                let uu____65568 =
                  let uu____65579 =
                    let uu____65588 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____65588  in
                  let uu____65589 =
                    let uu____65600 =
                      let uu____65609 =
                        let uu____65610 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____65610 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____65609  in
                    [uu____65600]  in
                  uu____65579 :: uu____65589  in
                uu____65558 :: uu____65568  in
              uu____65535 :: uu____65547  in
            uu____65511 :: uu____65524  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____65510
           in
        uu____65505 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_65674 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_65674.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_65674.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65693 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65693 with
    | (hd1,args) ->
        let uu____65738 =
          let uu____65751 =
            let uu____65752 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65752.FStar_Syntax_Syntax.n  in
          (uu____65751, args)  in
        (match uu____65738 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____65767)::(us,uu____65769)::(bs,uu____65771)::
            (t2,uu____65773)::(dcs,uu____65775)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____65840 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____65840
               (fun nm1  ->
                  let uu____65858 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____65858
                    (fun us1  ->
                       let uu____65872 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____65872
                         (fun bs1  ->
                            let uu____65878 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____65878
                              (fun t3  ->
                                 let uu____65884 =
                                   let uu____65892 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____65892 dcs  in
                                 FStar_Util.bind_opt uu____65884
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _65922  ->
                                           FStar_Pervasives_Native.Some
                                             _65922)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____65931)::(fvar1,uu____65933)::(univs1,uu____65935)::
            (ty,uu____65937)::(t2,uu____65939)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____66004 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____66004
               (fun r1  ->
                  let uu____66014 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____66014
                    (fun fvar2  ->
                       let uu____66020 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____66020
                         (fun univs2  ->
                            let uu____66034 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____66034
                              (fun ty1  ->
                                 let uu____66040 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____66040
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _66047  ->
                                           FStar_Pervasives_Native.Some
                                             _66047)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____66066 ->
             (if w
              then
                (let uu____66081 =
                   let uu____66087 =
                     let uu____66089 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____66089
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____66087)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____66081)
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
          let uu____66115 =
            let uu____66120 =
              let uu____66121 =
                let uu____66130 =
                  let uu____66131 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____66131  in
                FStar_Syntax_Syntax.as_arg uu____66130  in
              [uu____66121]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____66120
             in
          uu____66115 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____66151 =
            let uu____66156 =
              let uu____66157 =
                let uu____66166 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____66166  in
              let uu____66167 =
                let uu____66178 =
                  let uu____66187 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____66187  in
                [uu____66178]  in
              uu____66157 :: uu____66167  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____66156
             in
          uu____66151 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_66212 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_66212.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_66212.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____66233 = FStar_Syntax_Util.head_and_args t1  in
    match uu____66233 with
    | (hd1,args) ->
        let uu____66278 =
          let uu____66291 =
            let uu____66292 = FStar_Syntax_Util.un_uinst hd1  in
            uu____66292.FStar_Syntax_Syntax.n  in
          (uu____66291, args)  in
        (match uu____66278 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____66322)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____66347 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____66347
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _66354  -> FStar_Pervasives_Native.Some _66354)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____66357)::(e2,uu____66359)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____66394 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____66394
               (fun e11  ->
                  let uu____66400 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____66400
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _66407  -> FStar_Pervasives_Native.Some _66407)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____66408 ->
             (if w
              then
                (let uu____66423 =
                   let uu____66429 =
                     let uu____66431 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____66431
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____66429)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____66423)
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
    let uu____66455 =
      let uu____66460 =
        let uu____66461 =
          let uu____66470 =
            let uu____66471 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____66471  in
          FStar_Syntax_Syntax.as_arg uu____66470  in
        [uu____66461]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____66460
       in
    uu____66455 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____66495 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____66495 with
    | (bv,aq) ->
        let uu____66502 =
          let uu____66507 =
            let uu____66508 =
              let uu____66517 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____66517  in
            let uu____66518 =
              let uu____66529 =
                let uu____66538 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____66538  in
              [uu____66529]  in
            uu____66508 :: uu____66518  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____66507
           in
        uu____66502 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____66570 =
      let uu____66575 =
        let uu____66576 =
          let uu____66585 =
            let uu____66586 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____66593 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____66586 i.FStar_Syntax_Syntax.rng uu____66593  in
          FStar_Syntax_Syntax.as_arg uu____66585  in
        [uu____66576]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____66575
       in
    uu____66570 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____66623 =
      let uu____66628 =
        let uu____66629 =
          let uu____66638 =
            let uu____66639 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____66639  in
          FStar_Syntax_Syntax.as_arg uu____66638  in
        [uu____66629]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____66628
       in
    uu____66623 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____66669 =
      let uu____66674 =
        let uu____66675 =
          let uu____66684 =
            let uu____66685 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____66685  in
          FStar_Syntax_Syntax.as_arg uu____66684  in
        [uu____66675]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____66674
       in
    uu____66669 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  