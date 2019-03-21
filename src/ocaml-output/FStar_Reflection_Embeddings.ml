open Prims
let mk_emb :
  'Auu____59387 .
    (FStar_Range.range -> 'Auu____59387 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____59387 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____59387 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____59431 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____59431
  
let embed :
  'Auu____59458 .
    'Auu____59458 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____59458 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____59478 = FStar_Syntax_Embeddings.embed e x  in
        uu____59478 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____59496 .
    Prims.bool ->
      'Auu____59496 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____59496 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____59520 = FStar_Syntax_Embeddings.unembed e x  in
        uu____59520 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____59558 =
      let uu____59559 = FStar_Syntax_Subst.compress t  in
      uu____59559.FStar_Syntax_Syntax.n  in
    match uu____59558 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____59565;
          FStar_Syntax_Syntax.rng = uu____59566;_}
        ->
        let uu____59569 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59569
    | uu____59570 ->
        (if w
         then
           (let uu____59573 =
              let uu____59579 =
                let uu____59581 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____59581  in
              (FStar_Errors.Warning_NotEmbedded, uu____59579)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59573)
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
    let uu____59618 =
      let uu____59619 = FStar_Syntax_Subst.compress t  in
      uu____59619.FStar_Syntax_Syntax.n  in
    match uu____59618 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____59625;
          FStar_Syntax_Syntax.rng = uu____59626;_}
        ->
        let uu____59629 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59629
    | uu____59630 ->
        (if w
         then
           (let uu____59633 =
              let uu____59639 =
                let uu____59641 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____59641
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____59639)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59633)
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
          let uu____59693 = f x  in
          FStar_Util.bind_opt uu____59693
            (fun x1  ->
               let uu____59701 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59701
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
        let uu____59770 =
          mapM_opt
            (fun uu____59783  ->
               match uu____59783 with
               | (bv,e) ->
                   let uu____59792 = unembed_term w e  in
                   FStar_Util.bind_opt uu____59792
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____59770
          (fun s  ->
             let uu____59806 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____59806)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____59808 =
        let uu____59809 = FStar_Syntax_Subst.compress t1  in
        uu____59809.FStar_Syntax_Syntax.n  in
      match uu____59808 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____59820 ->
          (if w
           then
             (let uu____59823 =
                let uu____59829 =
                  let uu____59831 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____59831
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____59829)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____59823)
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
          let uu____59866 =
            let uu____59871 =
              let uu____59872 =
                let uu____59881 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____59881  in
              [uu____59872]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____59871
             in
          uu____59866 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_59898 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_59898.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_59898.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____59919 = FStar_Syntax_Util.head_and_args t1  in
    match uu____59919 with
    | (hd1,args) ->
        let uu____59964 =
          let uu____59979 =
            let uu____59980 = FStar_Syntax_Util.un_uinst hd1  in
            uu____59980.FStar_Syntax_Syntax.n  in
          (uu____59979, args)  in
        (match uu____59964 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____60035)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____60070 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____60070
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____60075 ->
             (if w
              then
                (let uu____60092 =
                   let uu____60098 =
                     let uu____60100 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____60100
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60098)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60092)
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
    let uu____60140 =
      let uu____60141 = FStar_Syntax_Subst.compress t  in
      uu____60141.FStar_Syntax_Syntax.n  in
    match uu____60140 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____60147;
          FStar_Syntax_Syntax.rng = uu____60148;_}
        ->
        let uu____60151 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60151
    | uu____60152 ->
        (if w
         then
           (let uu____60155 =
              let uu____60161 =
                let uu____60163 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____60163  in
              (FStar_Errors.Warning_NotEmbedded, uu____60161)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60155)
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
    let uu____60200 =
      let uu____60201 = FStar_Syntax_Subst.compress t  in
      uu____60201.FStar_Syntax_Syntax.n  in
    match uu____60200 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____60207;
          FStar_Syntax_Syntax.rng = uu____60208;_}
        ->
        let uu____60211 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60211
    | uu____60212 ->
        (if w
         then
           (let uu____60215 =
              let uu____60221 =
                let uu____60223 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____60223  in
              (FStar_Errors.Warning_NotEmbedded, uu____60221)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60215)
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
    let uu____60260 =
      let uu____60261 = FStar_Syntax_Subst.compress t  in
      uu____60261.FStar_Syntax_Syntax.n  in
    match uu____60260 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____60267;
          FStar_Syntax_Syntax.rng = uu____60268;_}
        ->
        let uu____60271 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60271
    | uu____60272 ->
        (if w
         then
           (let uu____60275 =
              let uu____60281 =
                let uu____60283 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____60283  in
              (FStar_Errors.Warning_NotEmbedded, uu____60281)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60275)
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
          let uu____60309 =
            let uu____60314 =
              let uu____60315 =
                let uu____60324 =
                  let uu____60325 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____60325  in
                FStar_Syntax_Syntax.as_arg uu____60324  in
              [uu____60315]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____60314
             in
          uu____60309 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____60345 =
            let uu____60350 =
              let uu____60351 =
                let uu____60360 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____60360  in
              [uu____60351]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____60350
             in
          uu____60345 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____60379 =
            let uu____60384 =
              let uu____60385 =
                let uu____60394 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____60394  in
              [uu____60385]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____60384
             in
          uu____60379 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____60412 =
            let uu____60417 =
              let uu____60418 =
                let uu____60427 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____60427  in
              [uu____60418]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____60417
             in
          uu____60412 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_60447 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_60447.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_60447.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____60468 = FStar_Syntax_Util.head_and_args t1  in
    match uu____60468 with
    | (hd1,args) ->
        let uu____60513 =
          let uu____60528 =
            let uu____60529 = FStar_Syntax_Util.un_uinst hd1  in
            uu____60529.FStar_Syntax_Syntax.n  in
          (uu____60528, args)  in
        (match uu____60513 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____60603)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____60638 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____60638
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _60645  -> FStar_Pervasives_Native.Some _60645)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____60648)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____60683 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____60683
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _60694  -> FStar_Pervasives_Native.Some _60694)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____60697)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____60732 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____60732
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _60739  -> FStar_Pervasives_Native.Some _60739)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _60761  -> FStar_Pervasives_Native.Some _60761)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____60764)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____60799 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____60799
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _60818  -> FStar_Pervasives_Native.Some _60818)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____60819 ->
             (if w
              then
                (let uu____60836 =
                   let uu____60842 =
                     let uu____60844 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____60844
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60842)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60836)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____60857  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60870 =
            let uu____60875 =
              let uu____60876 =
                let uu____60885 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____60885  in
              [uu____60876]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____60875
             in
          uu____60870 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60908 =
            let uu____60913 =
              let uu____60914 =
                let uu____60923 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____60923  in
              let uu____60924 =
                let uu____60935 =
                  let uu____60944 =
                    let uu____60945 =
                      let uu____60950 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____60950  in
                    embed uu____60945 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____60944  in
                [uu____60935]  in
              uu____60914 :: uu____60924  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____60913
             in
          uu____60908 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60980 =
            let uu____60985 =
              let uu____60986 =
                let uu____60995 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____60995  in
              [uu____60986]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____60985
             in
          uu____60980 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____61013 =
            let uu____61018 =
              let uu____61019 =
                let uu____61028 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61028  in
              [uu____61019]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____61018
             in
          uu____61013 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____61047 =
            let uu____61052 =
              let uu____61053 =
                let uu____61062 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61062  in
              let uu____61063 =
                let uu____61074 =
                  let uu____61083 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____61083  in
                [uu____61074]  in
              uu____61053 :: uu____61063  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____61052
             in
          uu____61047 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____61126 = FStar_Syntax_Util.head_and_args t1  in
      match uu____61126 with
      | (hd1,args) ->
          let uu____61171 =
            let uu____61184 =
              let uu____61185 = FStar_Syntax_Util.un_uinst hd1  in
              uu____61185.FStar_Syntax_Syntax.n  in
            (uu____61184, args)  in
          (match uu____61171 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____61200)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____61225 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____61225
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _61232  -> FStar_Pervasives_Native.Some _61232)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____61235)::(ps,uu____61237)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____61272 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____61272
                 (fun f1  ->
                    let uu____61278 =
                      let uu____61283 =
                        let uu____61288 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____61288  in
                      unembed' w uu____61283 ps  in
                    FStar_Util.bind_opt uu____61278
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _61301  ->
                              FStar_Pervasives_Native.Some _61301)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61306)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____61331 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61331
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61338  -> FStar_Pervasives_Native.Some _61338)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61341)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____61366 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61366
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61373  -> FStar_Pervasives_Native.Some _61373)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____61376)::(t2,uu____61378)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____61413 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61413
                 (fun bv1  ->
                    let uu____61419 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____61419
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _61426  ->
                              FStar_Pervasives_Native.Some _61426)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____61427 ->
               (if w
                then
                  (let uu____61442 =
                     let uu____61448 =
                       let uu____61450 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____61450
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____61448)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____61442)
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
    let uu____61477 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____61477
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____61492 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____61492 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61515 =
            let uu____61520 =
              let uu____61521 =
                let uu____61530 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61530  in
              [uu____61521]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____61520
             in
          uu____61515 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____61548 =
            let uu____61553 =
              let uu____61554 =
                let uu____61563 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61563  in
              [uu____61554]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____61553
             in
          uu____61548 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61581 =
            let uu____61586 =
              let uu____61587 =
                let uu____61596 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61596  in
              [uu____61587]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____61586
             in
          uu____61581 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61615 =
            let uu____61620 =
              let uu____61621 =
                let uu____61630 =
                  let uu____61631 = e_term_aq aq  in
                  embed uu____61631 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____61630  in
              let uu____61634 =
                let uu____61645 =
                  let uu____61654 =
                    let uu____61655 = e_argv_aq aq  in
                    embed uu____61655 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____61654  in
                [uu____61645]  in
              uu____61621 :: uu____61634  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____61620
             in
          uu____61615 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____61692 =
            let uu____61697 =
              let uu____61698 =
                let uu____61707 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61707  in
              let uu____61708 =
                let uu____61719 =
                  let uu____61728 =
                    let uu____61729 = e_term_aq aq  in
                    embed uu____61729 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61728  in
                [uu____61719]  in
              uu____61698 :: uu____61708  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____61697
             in
          uu____61692 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61758 =
            let uu____61763 =
              let uu____61764 =
                let uu____61773 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61773  in
              let uu____61774 =
                let uu____61785 =
                  let uu____61794 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____61794  in
                [uu____61785]  in
              uu____61764 :: uu____61774  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____61763
             in
          uu____61758 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61820 =
            let uu____61825 =
              let uu____61826 =
                let uu____61835 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____61835  in
              [uu____61826]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____61825
             in
          uu____61820 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____61854 =
            let uu____61859 =
              let uu____61860 =
                let uu____61869 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61869  in
              let uu____61870 =
                let uu____61881 =
                  let uu____61890 =
                    let uu____61891 = e_term_aq aq  in
                    embed uu____61891 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61890  in
                [uu____61881]  in
              uu____61860 :: uu____61870  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____61859
             in
          uu____61854 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61919 =
            let uu____61924 =
              let uu____61925 =
                let uu____61934 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____61934  in
              [uu____61925]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____61924
             in
          uu____61919 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61953 =
            let uu____61958 =
              let uu____61959 =
                let uu____61968 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____61968  in
              let uu____61969 =
                let uu____61980 =
                  let uu____61989 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____61989  in
                [uu____61980]  in
              uu____61959 :: uu____61969  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____61958
             in
          uu____61953 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____62024 =
            let uu____62029 =
              let uu____62030 =
                let uu____62039 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____62039  in
              let uu____62041 =
                let uu____62052 =
                  let uu____62061 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____62061  in
                let uu____62062 =
                  let uu____62073 =
                    let uu____62082 =
                      let uu____62083 = e_term_aq aq  in
                      embed uu____62083 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____62082  in
                  let uu____62086 =
                    let uu____62097 =
                      let uu____62106 =
                        let uu____62107 = e_term_aq aq  in
                        embed uu____62107 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____62106  in
                    [uu____62097]  in
                  uu____62073 :: uu____62086  in
                uu____62052 :: uu____62062  in
              uu____62030 :: uu____62041  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____62029
             in
          uu____62024 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____62156 =
            let uu____62161 =
              let uu____62162 =
                let uu____62171 =
                  let uu____62172 = e_term_aq aq  in embed uu____62172 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____62171  in
              let uu____62175 =
                let uu____62186 =
                  let uu____62195 =
                    let uu____62196 =
                      let uu____62205 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____62205  in
                    embed uu____62196 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____62195  in
                [uu____62186]  in
              uu____62162 :: uu____62175  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____62161
             in
          uu____62156 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____62253 =
            let uu____62258 =
              let uu____62259 =
                let uu____62268 =
                  let uu____62269 = e_term_aq aq  in embed uu____62269 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62268  in
              let uu____62272 =
                let uu____62283 =
                  let uu____62292 =
                    let uu____62293 = e_term_aq aq  in
                    embed uu____62293 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____62292  in
                let uu____62296 =
                  let uu____62307 =
                    let uu____62316 =
                      let uu____62317 =
                        let uu____62322 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62322  in
                      embed uu____62317 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62316  in
                  [uu____62307]  in
                uu____62283 :: uu____62296  in
              uu____62259 :: uu____62272  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____62258
             in
          uu____62253 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____62366 =
            let uu____62371 =
              let uu____62372 =
                let uu____62381 =
                  let uu____62382 = e_term_aq aq  in embed uu____62382 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62381  in
              let uu____62385 =
                let uu____62396 =
                  let uu____62405 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____62405  in
                let uu____62406 =
                  let uu____62417 =
                    let uu____62426 =
                      let uu____62427 =
                        let uu____62432 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62432  in
                      embed uu____62427 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62426  in
                  [uu____62417]  in
                uu____62396 :: uu____62406  in
              uu____62372 :: uu____62385  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____62371
             in
          uu____62366 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_62469 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_62469.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_62469.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____62487 = FStar_Syntax_Util.head_and_args t  in
      match uu____62487 with
      | (hd1,args) ->
          let uu____62532 =
            let uu____62545 =
              let uu____62546 = FStar_Syntax_Util.un_uinst hd1  in
              uu____62546.FStar_Syntax_Syntax.n  in
            (uu____62545, args)  in
          (match uu____62532 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62561)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____62586 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62586
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62593  -> FStar_Pervasives_Native.Some _62593)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62596)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____62621 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62621
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62628  -> FStar_Pervasives_Native.Some _62628)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____62631)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____62656 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____62656
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _62663  -> FStar_Pervasives_Native.Some _62663)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____62666)::(r,uu____62668)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____62703 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____62703
                 (fun l1  ->
                    let uu____62709 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____62709
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _62716  ->
                              FStar_Pervasives_Native.Some _62716)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62719)::(t1,uu____62721)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____62756 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62756
                 (fun b1  ->
                    let uu____62762 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62762
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62769  ->
                              FStar_Pervasives_Native.Some _62769)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62772)::(t1,uu____62774)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____62809 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62809
                 (fun b1  ->
                    let uu____62815 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____62815
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _62822  ->
                              FStar_Pervasives_Native.Some _62822)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____62825)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____62850 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____62850
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _62857  -> FStar_Pervasives_Native.Some _62857)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62860)::(t1,uu____62862)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____62897 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62897
                 (fun b1  ->
                    let uu____62903 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62903
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62910  ->
                              FStar_Pervasives_Native.Some _62910)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____62913)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____62938 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____62938
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _62945  -> FStar_Pervasives_Native.Some _62945)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____62948)::(l,uu____62950)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____62985 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____62985
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _62994  -> FStar_Pervasives_Native.Some _62994)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____62997)::(b,uu____62999)::(t1,uu____63001)::
              (t2,uu____63003)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____63058 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____63058
                 (fun r1  ->
                    let uu____63068 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____63068
                      (fun b1  ->
                         let uu____63074 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____63074
                           (fun t11  ->
                              let uu____63080 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____63080
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _63087  ->
                                        FStar_Pervasives_Native.Some _63087)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____63091)::(brs,uu____63093)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____63128 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____63128
                 (fun t2  ->
                    let uu____63134 =
                      let uu____63139 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____63139 brs  in
                    FStar_Util.bind_opt uu____63134
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _63154  ->
                              FStar_Pervasives_Native.Some _63154)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63159)::(t1,uu____63161)::(tacopt,uu____63163)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____63208 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63208
                 (fun e1  ->
                    let uu____63214 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____63214
                      (fun t2  ->
                         let uu____63220 =
                           let uu____63225 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63225 tacopt  in
                         FStar_Util.bind_opt uu____63220
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63240  ->
                                   FStar_Pervasives_Native.Some _63240)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63245)::(c,uu____63247)::(tacopt,uu____63249)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____63294 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63294
                 (fun e1  ->
                    let uu____63300 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____63300
                      (fun c1  ->
                         let uu____63306 =
                           let uu____63311 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63311 tacopt  in
                         FStar_Util.bind_opt uu____63306
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63326  ->
                                   FStar_Pervasives_Native.Some _63326)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _63346  -> FStar_Pervasives_Native.Some _63346)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____63347 ->
               (if w
                then
                  (let uu____63362 =
                     let uu____63368 =
                       let uu____63370 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____63370
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____63368)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____63362)
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
    let uu____63399 =
      let uu____63404 =
        let uu____63405 =
          let uu____63414 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____63414  in
        let uu____63416 =
          let uu____63427 =
            let uu____63436 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____63436  in
          let uu____63437 =
            let uu____63448 =
              let uu____63457 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____63457  in
            [uu____63448]  in
          uu____63427 :: uu____63437  in
        uu____63405 :: uu____63416  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____63404
       in
    uu____63399 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63508 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63508 with
    | (hd1,args) ->
        let uu____63553 =
          let uu____63566 =
            let uu____63567 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63567.FStar_Syntax_Syntax.n  in
          (uu____63566, args)  in
        (match uu____63553 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____63582)::(idx,uu____63584)::(s,uu____63586)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____63631 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____63631
               (fun nm1  ->
                  let uu____63641 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____63641
                    (fun idx1  ->
                       let uu____63647 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____63647
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _63654  ->
                                 FStar_Pervasives_Native.Some _63654)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____63655 ->
             (if w
              then
                (let uu____63670 =
                   let uu____63676 =
                     let uu____63678 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____63678
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____63676)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____63670)
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
        let uu____63704 =
          let uu____63709 =
            let uu____63710 =
              let uu____63719 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____63719  in
            let uu____63720 =
              let uu____63731 =
                let uu____63740 =
                  let uu____63741 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____63741 rng md  in
                FStar_Syntax_Syntax.as_arg uu____63740  in
              [uu____63731]  in
            uu____63710 :: uu____63720  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____63709
           in
        uu____63704 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____63777 =
          let uu____63782 =
            let uu____63783 =
              let uu____63792 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____63792  in
            let uu____63793 =
              let uu____63804 =
                let uu____63813 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____63813  in
              [uu____63804]  in
            uu____63783 :: uu____63793  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____63782
           in
        uu____63777 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_63838 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_63838.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_63838.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63857 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63857 with
    | (hd1,args) ->
        let uu____63902 =
          let uu____63915 =
            let uu____63916 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63916.FStar_Syntax_Syntax.n  in
          (uu____63915, args)  in
        (match uu____63902 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____63931)::(md,uu____63933)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____63968 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____63968
               (fun t3  ->
                  let uu____63974 =
                    let uu____63979 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____63979 md  in
                  FStar_Util.bind_opt uu____63974
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _63994  -> FStar_Pervasives_Native.Some _63994)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____63999)::(post,uu____64001)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____64036 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____64036
               (fun pre1  ->
                  let uu____64042 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____64042
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _64049  -> FStar_Pervasives_Native.Some _64049)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _64067  -> FStar_Pervasives_Native.Some _64067)
               FStar_Reflection_Data.C_Unknown
         | uu____64068 ->
             (if w
              then
                (let uu____64083 =
                   let uu____64089 =
                     let uu____64091 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____64091
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64089)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64083)
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
    let uu___1175_64116 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_64116.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_64116.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64137 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64137 with
    | (hd1,args) ->
        let uu____64182 =
          let uu____64197 =
            let uu____64198 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64198.FStar_Syntax_Syntax.n  in
          (uu____64197, args)  in
        (match uu____64182 with
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
         | uu____64270 ->
             (if w
              then
                (let uu____64287 =
                   let uu____64293 =
                     let uu____64295 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____64295
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64293)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64287)
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
    let uu____64332 =
      let uu____64333 = FStar_Syntax_Subst.compress t  in
      uu____64333.FStar_Syntax_Syntax.n  in
    match uu____64332 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____64339;
          FStar_Syntax_Syntax.rng = uu____64340;_}
        ->
        let uu____64343 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64343
    | uu____64344 ->
        (if w
         then
           (let uu____64347 =
              let uu____64353 =
                let uu____64355 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____64355
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64353)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64347)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____64395 uu____64396 =
    let uu____64398 =
      let uu____64404 = FStar_Ident.range_of_id i  in
      let uu____64405 = FStar_Ident.text_of_id i  in
      (uu____64404, uu____64405)  in
    embed repr rng uu____64398  in
  let unembed_ident t w uu____64432 =
    let uu____64437 = unembed' w repr t  in
    match uu____64437 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____64461 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____64461
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____64468 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____64468
  
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
        let uu____64507 =
          let uu____64512 =
            let uu____64513 =
              let uu____64522 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____64522  in
            let uu____64524 =
              let uu____64535 =
                let uu____64544 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____64544  in
              let uu____64545 =
                let uu____64556 =
                  let uu____64565 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____64565  in
                let uu____64568 =
                  let uu____64579 =
                    let uu____64588 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____64588  in
                  let uu____64589 =
                    let uu____64600 =
                      let uu____64609 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____64609  in
                    [uu____64600]  in
                  uu____64579 :: uu____64589  in
                uu____64556 :: uu____64568  in
              uu____64535 :: uu____64545  in
            uu____64513 :: uu____64524  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____64512
           in
        uu____64507 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____64660 =
          let uu____64665 =
            let uu____64666 =
              let uu____64675 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64675  in
            let uu____64679 =
              let uu____64690 =
                let uu____64699 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____64699  in
              [uu____64690]  in
            uu____64666 :: uu____64679  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____64665
           in
        uu____64660 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____64741 =
          let uu____64746 =
            let uu____64747 =
              let uu____64756 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64756  in
            let uu____64760 =
              let uu____64771 =
                let uu____64780 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____64780  in
              let uu____64783 =
                let uu____64794 =
                  let uu____64803 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____64803  in
                let uu____64804 =
                  let uu____64815 =
                    let uu____64824 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____64824  in
                  let uu____64825 =
                    let uu____64836 =
                      let uu____64845 =
                        let uu____64846 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____64846 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____64845  in
                    [uu____64836]  in
                  uu____64815 :: uu____64825  in
                uu____64794 :: uu____64804  in
              uu____64771 :: uu____64783  in
            uu____64747 :: uu____64760  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____64746
           in
        uu____64741 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_64910 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_64910.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_64910.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64929 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64929 with
    | (hd1,args) ->
        let uu____64974 =
          let uu____64987 =
            let uu____64988 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64988.FStar_Syntax_Syntax.n  in
          (uu____64987, args)  in
        (match uu____64974 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____65003)::(us,uu____65005)::(bs,uu____65007)::
            (t2,uu____65009)::(dcs,uu____65011)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____65076 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____65076
               (fun nm1  ->
                  let uu____65094 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____65094
                    (fun us1  ->
                       let uu____65108 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____65108
                         (fun bs1  ->
                            let uu____65114 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____65114
                              (fun t3  ->
                                 let uu____65120 =
                                   let uu____65128 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____65128 dcs  in
                                 FStar_Util.bind_opt uu____65120
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _65158  ->
                                           FStar_Pervasives_Native.Some
                                             _65158)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____65167)::(fvar1,uu____65169)::(univs1,uu____65171)::
            (ty,uu____65173)::(t2,uu____65175)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____65240 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____65240
               (fun r1  ->
                  let uu____65250 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____65250
                    (fun fvar2  ->
                       let uu____65256 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____65256
                         (fun univs2  ->
                            let uu____65270 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____65270
                              (fun ty1  ->
                                 let uu____65276 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____65276
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _65283  ->
                                           FStar_Pervasives_Native.Some
                                             _65283)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____65302 ->
             (if w
              then
                (let uu____65317 =
                   let uu____65323 =
                     let uu____65325 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____65325
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65323)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65317)
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
          let uu____65351 =
            let uu____65356 =
              let uu____65357 =
                let uu____65366 =
                  let uu____65367 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65367  in
                FStar_Syntax_Syntax.as_arg uu____65366  in
              [uu____65357]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____65356
             in
          uu____65351 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____65387 =
            let uu____65392 =
              let uu____65393 =
                let uu____65402 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____65402  in
              let uu____65403 =
                let uu____65414 =
                  let uu____65423 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____65423  in
                [uu____65414]  in
              uu____65393 :: uu____65403  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____65392
             in
          uu____65387 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_65448 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_65448.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_65448.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65469 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65469 with
    | (hd1,args) ->
        let uu____65514 =
          let uu____65527 =
            let uu____65528 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65528.FStar_Syntax_Syntax.n  in
          (uu____65527, args)  in
        (match uu____65514 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65558)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____65583 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65583
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65590  -> FStar_Pervasives_Native.Some _65590)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____65593)::(e2,uu____65595)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____65630 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____65630
               (fun e11  ->
                  let uu____65636 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____65636
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _65643  -> FStar_Pervasives_Native.Some _65643)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____65644 ->
             (if w
              then
                (let uu____65659 =
                   let uu____65665 =
                     let uu____65667 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____65667
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65665)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65659)
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
    let uu____65691 =
      let uu____65696 =
        let uu____65697 =
          let uu____65706 =
            let uu____65707 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____65707  in
          FStar_Syntax_Syntax.as_arg uu____65706  in
        [uu____65697]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____65696
       in
    uu____65691 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65731 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____65731 with
    | (bv,aq) ->
        let uu____65738 =
          let uu____65743 =
            let uu____65744 =
              let uu____65753 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____65753  in
            let uu____65754 =
              let uu____65765 =
                let uu____65774 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____65774  in
              [uu____65765]  in
            uu____65744 :: uu____65754  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____65743
           in
        uu____65738 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65806 =
      let uu____65811 =
        let uu____65812 =
          let uu____65821 =
            let uu____65822 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____65829 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____65822 i.FStar_Syntax_Syntax.rng uu____65829  in
          FStar_Syntax_Syntax.as_arg uu____65821  in
        [uu____65812]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____65811
       in
    uu____65806 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65859 =
      let uu____65864 =
        let uu____65865 =
          let uu____65874 =
            let uu____65875 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____65875  in
          FStar_Syntax_Syntax.as_arg uu____65874  in
        [uu____65865]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____65864
       in
    uu____65859 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65905 =
      let uu____65910 =
        let uu____65911 =
          let uu____65920 =
            let uu____65921 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____65921  in
          FStar_Syntax_Syntax.as_arg uu____65920  in
        [uu____65911]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____65910
       in
    uu____65905 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  