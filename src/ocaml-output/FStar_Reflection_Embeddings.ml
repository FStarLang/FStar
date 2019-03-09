open Prims
let mk_emb :
  'Auu____59367 .
    (FStar_Range.range -> 'Auu____59367 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____59367 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____59367 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____59411 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____59411
  
let embed :
  'Auu____59438 .
    'Auu____59438 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____59438 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____59458 = FStar_Syntax_Embeddings.embed e x  in
        uu____59458 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____59476 .
    Prims.bool ->
      'Auu____59476 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____59476 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____59500 = FStar_Syntax_Embeddings.unembed e x  in
        uu____59500 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____59538 =
      let uu____59539 = FStar_Syntax_Subst.compress t  in
      uu____59539.FStar_Syntax_Syntax.n  in
    match uu____59538 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____59545;
          FStar_Syntax_Syntax.rng = uu____59546;_}
        ->
        let uu____59549 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59549
    | uu____59550 ->
        (if w
         then
           (let uu____59553 =
              let uu____59559 =
                let uu____59561 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____59561  in
              (FStar_Errors.Warning_NotEmbedded, uu____59559)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59553)
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
    let uu____59598 =
      let uu____59599 = FStar_Syntax_Subst.compress t  in
      uu____59599.FStar_Syntax_Syntax.n  in
    match uu____59598 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____59605;
          FStar_Syntax_Syntax.rng = uu____59606;_}
        ->
        let uu____59609 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59609
    | uu____59610 ->
        (if w
         then
           (let uu____59613 =
              let uu____59619 =
                let uu____59621 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____59621
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____59619)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59613)
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
          let uu____59673 = f x  in
          FStar_Util.bind_opt uu____59673
            (fun x1  ->
               let uu____59681 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59681
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
        let uu____59750 =
          mapM_opt
            (fun uu____59763  ->
               match uu____59763 with
               | (bv,e) ->
                   let uu____59772 = unembed_term w e  in
                   FStar_Util.bind_opt uu____59772
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____59750
          (fun s  ->
             let uu____59786 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____59786)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____59788 =
        let uu____59789 = FStar_Syntax_Subst.compress t1  in
        uu____59789.FStar_Syntax_Syntax.n  in
      match uu____59788 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____59800 ->
          (if w
           then
             (let uu____59803 =
                let uu____59809 =
                  let uu____59811 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____59811
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____59809)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____59803)
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
          let uu____59846 =
            let uu____59851 =
              let uu____59852 =
                let uu____59861 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____59861  in
              [uu____59852]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____59851
             in
          uu____59846 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_59878 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_59878.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_59878.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____59899 = FStar_Syntax_Util.head_and_args t1  in
    match uu____59899 with
    | (hd1,args) ->
        let uu____59944 =
          let uu____59959 =
            let uu____59960 = FStar_Syntax_Util.un_uinst hd1  in
            uu____59960.FStar_Syntax_Syntax.n  in
          (uu____59959, args)  in
        (match uu____59944 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____60015)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____60050 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____60050
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____60055 ->
             (if w
              then
                (let uu____60072 =
                   let uu____60078 =
                     let uu____60080 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____60080
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60078)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60072)
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
    let uu____60120 =
      let uu____60121 = FStar_Syntax_Subst.compress t  in
      uu____60121.FStar_Syntax_Syntax.n  in
    match uu____60120 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____60127;
          FStar_Syntax_Syntax.rng = uu____60128;_}
        ->
        let uu____60131 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60131
    | uu____60132 ->
        (if w
         then
           (let uu____60135 =
              let uu____60141 =
                let uu____60143 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____60143  in
              (FStar_Errors.Warning_NotEmbedded, uu____60141)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60135)
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
    let uu____60180 =
      let uu____60181 = FStar_Syntax_Subst.compress t  in
      uu____60181.FStar_Syntax_Syntax.n  in
    match uu____60180 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____60187;
          FStar_Syntax_Syntax.rng = uu____60188;_}
        ->
        let uu____60191 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60191
    | uu____60192 ->
        (if w
         then
           (let uu____60195 =
              let uu____60201 =
                let uu____60203 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____60203  in
              (FStar_Errors.Warning_NotEmbedded, uu____60201)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60195)
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
    let uu____60240 =
      let uu____60241 = FStar_Syntax_Subst.compress t  in
      uu____60241.FStar_Syntax_Syntax.n  in
    match uu____60240 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____60247;
          FStar_Syntax_Syntax.rng = uu____60248;_}
        ->
        let uu____60251 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60251
    | uu____60252 ->
        (if w
         then
           (let uu____60255 =
              let uu____60261 =
                let uu____60263 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____60263  in
              (FStar_Errors.Warning_NotEmbedded, uu____60261)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60255)
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
          let uu____60289 =
            let uu____60294 =
              let uu____60295 =
                let uu____60304 =
                  let uu____60305 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____60305  in
                FStar_Syntax_Syntax.as_arg uu____60304  in
              [uu____60295]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____60294
             in
          uu____60289 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____60325 =
            let uu____60330 =
              let uu____60331 =
                let uu____60340 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____60340  in
              [uu____60331]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____60330
             in
          uu____60325 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____60359 =
            let uu____60364 =
              let uu____60365 =
                let uu____60374 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____60374  in
              [uu____60365]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____60364
             in
          uu____60359 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____60392 =
            let uu____60397 =
              let uu____60398 =
                let uu____60407 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____60407  in
              [uu____60398]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____60397
             in
          uu____60392 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_60427 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_60427.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_60427.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____60448 = FStar_Syntax_Util.head_and_args t1  in
    match uu____60448 with
    | (hd1,args) ->
        let uu____60493 =
          let uu____60508 =
            let uu____60509 = FStar_Syntax_Util.un_uinst hd1  in
            uu____60509.FStar_Syntax_Syntax.n  in
          (uu____60508, args)  in
        (match uu____60493 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____60583)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____60618 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____60618
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _60625  -> FStar_Pervasives_Native.Some _60625)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____60628)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____60663 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____60663
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _60674  -> FStar_Pervasives_Native.Some _60674)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____60677)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____60712 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____60712
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _60719  -> FStar_Pervasives_Native.Some _60719)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _60741  -> FStar_Pervasives_Native.Some _60741)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____60744)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____60779 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____60779
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _60798  -> FStar_Pervasives_Native.Some _60798)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____60799 ->
             (if w
              then
                (let uu____60816 =
                   let uu____60822 =
                     let uu____60824 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____60824
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60822)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60816)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____60837  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60850 =
            let uu____60855 =
              let uu____60856 =
                let uu____60865 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____60865  in
              [uu____60856]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____60855
             in
          uu____60850 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60888 =
            let uu____60893 =
              let uu____60894 =
                let uu____60903 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____60903  in
              let uu____60904 =
                let uu____60915 =
                  let uu____60924 =
                    let uu____60925 =
                      let uu____60930 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____60930  in
                    embed uu____60925 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____60924  in
                [uu____60915]  in
              uu____60894 :: uu____60904  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____60893
             in
          uu____60888 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60960 =
            let uu____60965 =
              let uu____60966 =
                let uu____60975 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____60975  in
              [uu____60966]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____60965
             in
          uu____60960 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____60993 =
            let uu____60998 =
              let uu____60999 =
                let uu____61008 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61008  in
              [uu____60999]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____60998
             in
          uu____60993 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____61027 =
            let uu____61032 =
              let uu____61033 =
                let uu____61042 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61042  in
              let uu____61043 =
                let uu____61054 =
                  let uu____61063 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____61063  in
                [uu____61054]  in
              uu____61033 :: uu____61043  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____61032
             in
          uu____61027 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____61106 = FStar_Syntax_Util.head_and_args t1  in
      match uu____61106 with
      | (hd1,args) ->
          let uu____61151 =
            let uu____61164 =
              let uu____61165 = FStar_Syntax_Util.un_uinst hd1  in
              uu____61165.FStar_Syntax_Syntax.n  in
            (uu____61164, args)  in
          (match uu____61151 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____61180)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____61205 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____61205
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _61212  -> FStar_Pervasives_Native.Some _61212)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____61215)::(ps,uu____61217)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____61252 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____61252
                 (fun f1  ->
                    let uu____61258 =
                      let uu____61263 =
                        let uu____61268 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____61268  in
                      unembed' w uu____61263 ps  in
                    FStar_Util.bind_opt uu____61258
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _61281  ->
                              FStar_Pervasives_Native.Some _61281)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61286)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____61311 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61311
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61318  -> FStar_Pervasives_Native.Some _61318)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61321)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____61346 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61346
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61353  -> FStar_Pervasives_Native.Some _61353)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____61356)::(t2,uu____61358)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____61393 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61393
                 (fun bv1  ->
                    let uu____61399 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____61399
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _61406  ->
                              FStar_Pervasives_Native.Some _61406)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____61407 ->
               (if w
                then
                  (let uu____61422 =
                     let uu____61428 =
                       let uu____61430 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____61430
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____61428)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____61422)
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
    let uu____61457 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____61457
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____61472 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____61472 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61495 =
            let uu____61500 =
              let uu____61501 =
                let uu____61510 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61510  in
              [uu____61501]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____61500
             in
          uu____61495 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____61528 =
            let uu____61533 =
              let uu____61534 =
                let uu____61543 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61543  in
              [uu____61534]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____61533
             in
          uu____61528 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61561 =
            let uu____61566 =
              let uu____61567 =
                let uu____61576 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61576  in
              [uu____61567]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____61566
             in
          uu____61561 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61595 =
            let uu____61600 =
              let uu____61601 =
                let uu____61610 =
                  let uu____61611 = e_term_aq aq  in
                  embed uu____61611 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____61610  in
              let uu____61614 =
                let uu____61625 =
                  let uu____61634 =
                    let uu____61635 = e_argv_aq aq  in
                    embed uu____61635 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____61634  in
                [uu____61625]  in
              uu____61601 :: uu____61614  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____61600
             in
          uu____61595 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____61672 =
            let uu____61677 =
              let uu____61678 =
                let uu____61687 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61687  in
              let uu____61688 =
                let uu____61699 =
                  let uu____61708 =
                    let uu____61709 = e_term_aq aq  in
                    embed uu____61709 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61708  in
                [uu____61699]  in
              uu____61678 :: uu____61688  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____61677
             in
          uu____61672 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61738 =
            let uu____61743 =
              let uu____61744 =
                let uu____61753 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61753  in
              let uu____61754 =
                let uu____61765 =
                  let uu____61774 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____61774  in
                [uu____61765]  in
              uu____61744 :: uu____61754  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____61743
             in
          uu____61738 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61800 =
            let uu____61805 =
              let uu____61806 =
                let uu____61815 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____61815  in
              [uu____61806]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____61805
             in
          uu____61800 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____61834 =
            let uu____61839 =
              let uu____61840 =
                let uu____61849 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61849  in
              let uu____61850 =
                let uu____61861 =
                  let uu____61870 =
                    let uu____61871 = e_term_aq aq  in
                    embed uu____61871 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61870  in
                [uu____61861]  in
              uu____61840 :: uu____61850  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____61839
             in
          uu____61834 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61899 =
            let uu____61904 =
              let uu____61905 =
                let uu____61914 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____61914  in
              [uu____61905]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____61904
             in
          uu____61899 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61933 =
            let uu____61938 =
              let uu____61939 =
                let uu____61948 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____61948  in
              let uu____61949 =
                let uu____61960 =
                  let uu____61969 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____61969  in
                [uu____61960]  in
              uu____61939 :: uu____61949  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____61938
             in
          uu____61933 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____62004 =
            let uu____62009 =
              let uu____62010 =
                let uu____62019 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____62019  in
              let uu____62021 =
                let uu____62032 =
                  let uu____62041 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____62041  in
                let uu____62042 =
                  let uu____62053 =
                    let uu____62062 =
                      let uu____62063 = e_term_aq aq  in
                      embed uu____62063 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____62062  in
                  let uu____62066 =
                    let uu____62077 =
                      let uu____62086 =
                        let uu____62087 = e_term_aq aq  in
                        embed uu____62087 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____62086  in
                    [uu____62077]  in
                  uu____62053 :: uu____62066  in
                uu____62032 :: uu____62042  in
              uu____62010 :: uu____62021  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____62009
             in
          uu____62004 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____62136 =
            let uu____62141 =
              let uu____62142 =
                let uu____62151 =
                  let uu____62152 = e_term_aq aq  in embed uu____62152 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____62151  in
              let uu____62155 =
                let uu____62166 =
                  let uu____62175 =
                    let uu____62176 =
                      let uu____62185 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____62185  in
                    embed uu____62176 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____62175  in
                [uu____62166]  in
              uu____62142 :: uu____62155  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____62141
             in
          uu____62136 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____62233 =
            let uu____62238 =
              let uu____62239 =
                let uu____62248 =
                  let uu____62249 = e_term_aq aq  in embed uu____62249 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62248  in
              let uu____62252 =
                let uu____62263 =
                  let uu____62272 =
                    let uu____62273 = e_term_aq aq  in
                    embed uu____62273 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____62272  in
                let uu____62276 =
                  let uu____62287 =
                    let uu____62296 =
                      let uu____62297 =
                        let uu____62302 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62302  in
                      embed uu____62297 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62296  in
                  [uu____62287]  in
                uu____62263 :: uu____62276  in
              uu____62239 :: uu____62252  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____62238
             in
          uu____62233 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____62346 =
            let uu____62351 =
              let uu____62352 =
                let uu____62361 =
                  let uu____62362 = e_term_aq aq  in embed uu____62362 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62361  in
              let uu____62365 =
                let uu____62376 =
                  let uu____62385 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____62385  in
                let uu____62386 =
                  let uu____62397 =
                    let uu____62406 =
                      let uu____62407 =
                        let uu____62412 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62412  in
                      embed uu____62407 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62406  in
                  [uu____62397]  in
                uu____62376 :: uu____62386  in
              uu____62352 :: uu____62365  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____62351
             in
          uu____62346 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_62449 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_62449.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_62449.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____62467 = FStar_Syntax_Util.head_and_args t  in
      match uu____62467 with
      | (hd1,args) ->
          let uu____62512 =
            let uu____62525 =
              let uu____62526 = FStar_Syntax_Util.un_uinst hd1  in
              uu____62526.FStar_Syntax_Syntax.n  in
            (uu____62525, args)  in
          (match uu____62512 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62541)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____62566 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62566
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62573  -> FStar_Pervasives_Native.Some _62573)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62576)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____62601 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62601
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62608  -> FStar_Pervasives_Native.Some _62608)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____62611)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____62636 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____62636
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _62643  -> FStar_Pervasives_Native.Some _62643)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____62646)::(r,uu____62648)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____62683 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____62683
                 (fun l1  ->
                    let uu____62689 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____62689
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _62696  ->
                              FStar_Pervasives_Native.Some _62696)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62699)::(t1,uu____62701)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____62736 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62736
                 (fun b1  ->
                    let uu____62742 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62742
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62749  ->
                              FStar_Pervasives_Native.Some _62749)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62752)::(t1,uu____62754)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____62789 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62789
                 (fun b1  ->
                    let uu____62795 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____62795
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _62802  ->
                              FStar_Pervasives_Native.Some _62802)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____62805)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____62830 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____62830
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _62837  -> FStar_Pervasives_Native.Some _62837)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62840)::(t1,uu____62842)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____62877 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62877
                 (fun b1  ->
                    let uu____62883 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62883
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62890  ->
                              FStar_Pervasives_Native.Some _62890)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____62893)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____62918 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____62918
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _62925  -> FStar_Pervasives_Native.Some _62925)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____62928)::(l,uu____62930)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____62965 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____62965
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _62974  -> FStar_Pervasives_Native.Some _62974)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____62977)::(b,uu____62979)::(t1,uu____62981)::
              (t2,uu____62983)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____63038 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____63038
                 (fun r1  ->
                    let uu____63048 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____63048
                      (fun b1  ->
                         let uu____63054 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____63054
                           (fun t11  ->
                              let uu____63060 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____63060
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _63067  ->
                                        FStar_Pervasives_Native.Some _63067)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____63071)::(brs,uu____63073)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____63108 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____63108
                 (fun t2  ->
                    let uu____63114 =
                      let uu____63119 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____63119 brs  in
                    FStar_Util.bind_opt uu____63114
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _63134  ->
                              FStar_Pervasives_Native.Some _63134)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63139)::(t1,uu____63141)::(tacopt,uu____63143)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____63188 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63188
                 (fun e1  ->
                    let uu____63194 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____63194
                      (fun t2  ->
                         let uu____63200 =
                           let uu____63205 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63205 tacopt  in
                         FStar_Util.bind_opt uu____63200
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63220  ->
                                   FStar_Pervasives_Native.Some _63220)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63225)::(c,uu____63227)::(tacopt,uu____63229)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____63274 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63274
                 (fun e1  ->
                    let uu____63280 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____63280
                      (fun c1  ->
                         let uu____63286 =
                           let uu____63291 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63291 tacopt  in
                         FStar_Util.bind_opt uu____63286
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63306  ->
                                   FStar_Pervasives_Native.Some _63306)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _63326  -> FStar_Pervasives_Native.Some _63326)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____63327 ->
               (if w
                then
                  (let uu____63342 =
                     let uu____63348 =
                       let uu____63350 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____63350
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____63348)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____63342)
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
    let uu____63379 =
      let uu____63384 =
        let uu____63385 =
          let uu____63394 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____63394  in
        let uu____63396 =
          let uu____63407 =
            let uu____63416 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____63416  in
          let uu____63417 =
            let uu____63428 =
              let uu____63437 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____63437  in
            [uu____63428]  in
          uu____63407 :: uu____63417  in
        uu____63385 :: uu____63396  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____63384
       in
    uu____63379 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63488 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63488 with
    | (hd1,args) ->
        let uu____63533 =
          let uu____63546 =
            let uu____63547 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63547.FStar_Syntax_Syntax.n  in
          (uu____63546, args)  in
        (match uu____63533 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____63562)::(idx,uu____63564)::(s,uu____63566)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____63611 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____63611
               (fun nm1  ->
                  let uu____63621 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____63621
                    (fun idx1  ->
                       let uu____63627 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____63627
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _63634  ->
                                 FStar_Pervasives_Native.Some _63634)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____63635 ->
             (if w
              then
                (let uu____63650 =
                   let uu____63656 =
                     let uu____63658 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____63658
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____63656)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____63650)
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
        let uu____63684 =
          let uu____63689 =
            let uu____63690 =
              let uu____63699 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____63699  in
            let uu____63700 =
              let uu____63711 =
                let uu____63720 =
                  let uu____63721 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____63721 rng md  in
                FStar_Syntax_Syntax.as_arg uu____63720  in
              [uu____63711]  in
            uu____63690 :: uu____63700  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____63689
           in
        uu____63684 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____63757 =
          let uu____63762 =
            let uu____63763 =
              let uu____63772 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____63772  in
            let uu____63773 =
              let uu____63784 =
                let uu____63793 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____63793  in
              [uu____63784]  in
            uu____63763 :: uu____63773  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____63762
           in
        uu____63757 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_63818 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_63818.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_63818.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63837 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63837 with
    | (hd1,args) ->
        let uu____63882 =
          let uu____63895 =
            let uu____63896 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63896.FStar_Syntax_Syntax.n  in
          (uu____63895, args)  in
        (match uu____63882 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____63911)::(md,uu____63913)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____63948 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____63948
               (fun t3  ->
                  let uu____63954 =
                    let uu____63959 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____63959 md  in
                  FStar_Util.bind_opt uu____63954
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _63974  -> FStar_Pervasives_Native.Some _63974)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____63979)::(post,uu____63981)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____64016 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____64016
               (fun pre1  ->
                  let uu____64022 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____64022
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _64029  -> FStar_Pervasives_Native.Some _64029)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _64047  -> FStar_Pervasives_Native.Some _64047)
               FStar_Reflection_Data.C_Unknown
         | uu____64048 ->
             (if w
              then
                (let uu____64063 =
                   let uu____64069 =
                     let uu____64071 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____64071
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64069)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64063)
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
    let uu___1175_64096 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_64096.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_64096.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64117 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64117 with
    | (hd1,args) ->
        let uu____64162 =
          let uu____64177 =
            let uu____64178 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64178.FStar_Syntax_Syntax.n  in
          (uu____64177, args)  in
        (match uu____64162 with
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
         | uu____64250 ->
             (if w
              then
                (let uu____64267 =
                   let uu____64273 =
                     let uu____64275 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____64275
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64273)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64267)
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
    let uu____64312 =
      let uu____64313 = FStar_Syntax_Subst.compress t  in
      uu____64313.FStar_Syntax_Syntax.n  in
    match uu____64312 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____64319;
          FStar_Syntax_Syntax.rng = uu____64320;_}
        ->
        let uu____64323 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64323
    | uu____64324 ->
        (if w
         then
           (let uu____64327 =
              let uu____64333 =
                let uu____64335 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____64335
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64333)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64327)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____64375 uu____64376 =
    let uu____64378 =
      let uu____64384 = FStar_Ident.range_of_id i  in
      let uu____64385 = FStar_Ident.text_of_id i  in
      (uu____64384, uu____64385)  in
    embed repr rng uu____64378  in
  let unembed_ident t w uu____64412 =
    let uu____64417 = unembed' w repr t  in
    match uu____64417 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____64441 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____64441
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____64448 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____64448
  
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
        let uu____64487 =
          let uu____64492 =
            let uu____64493 =
              let uu____64502 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____64502  in
            let uu____64504 =
              let uu____64515 =
                let uu____64524 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____64524  in
              let uu____64525 =
                let uu____64536 =
                  let uu____64545 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____64545  in
                let uu____64548 =
                  let uu____64559 =
                    let uu____64568 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____64568  in
                  let uu____64569 =
                    let uu____64580 =
                      let uu____64589 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____64589  in
                    [uu____64580]  in
                  uu____64559 :: uu____64569  in
                uu____64536 :: uu____64548  in
              uu____64515 :: uu____64525  in
            uu____64493 :: uu____64504  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____64492
           in
        uu____64487 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____64640 =
          let uu____64645 =
            let uu____64646 =
              let uu____64655 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64655  in
            let uu____64659 =
              let uu____64670 =
                let uu____64679 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____64679  in
              [uu____64670]  in
            uu____64646 :: uu____64659  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____64645
           in
        uu____64640 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____64721 =
          let uu____64726 =
            let uu____64727 =
              let uu____64736 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64736  in
            let uu____64740 =
              let uu____64751 =
                let uu____64760 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____64760  in
              let uu____64763 =
                let uu____64774 =
                  let uu____64783 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____64783  in
                let uu____64784 =
                  let uu____64795 =
                    let uu____64804 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____64804  in
                  let uu____64805 =
                    let uu____64816 =
                      let uu____64825 =
                        let uu____64826 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____64826 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____64825  in
                    [uu____64816]  in
                  uu____64795 :: uu____64805  in
                uu____64774 :: uu____64784  in
              uu____64751 :: uu____64763  in
            uu____64727 :: uu____64740  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____64726
           in
        uu____64721 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_64890 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_64890.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_64890.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64909 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64909 with
    | (hd1,args) ->
        let uu____64954 =
          let uu____64967 =
            let uu____64968 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64968.FStar_Syntax_Syntax.n  in
          (uu____64967, args)  in
        (match uu____64954 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____64983)::(us,uu____64985)::(bs,uu____64987)::
            (t2,uu____64989)::(dcs,uu____64991)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____65056 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____65056
               (fun nm1  ->
                  let uu____65074 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____65074
                    (fun us1  ->
                       let uu____65088 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____65088
                         (fun bs1  ->
                            let uu____65094 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____65094
                              (fun t3  ->
                                 let uu____65100 =
                                   let uu____65108 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____65108 dcs  in
                                 FStar_Util.bind_opt uu____65100
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _65138  ->
                                           FStar_Pervasives_Native.Some
                                             _65138)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____65147)::(fvar1,uu____65149)::(univs1,uu____65151)::
            (ty,uu____65153)::(t2,uu____65155)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____65220 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____65220
               (fun r1  ->
                  let uu____65230 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____65230
                    (fun fvar2  ->
                       let uu____65236 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____65236
                         (fun univs2  ->
                            let uu____65250 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____65250
                              (fun ty1  ->
                                 let uu____65256 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____65256
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _65263  ->
                                           FStar_Pervasives_Native.Some
                                             _65263)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____65282 ->
             (if w
              then
                (let uu____65297 =
                   let uu____65303 =
                     let uu____65305 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____65305
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65303)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65297)
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
          let uu____65331 =
            let uu____65336 =
              let uu____65337 =
                let uu____65346 =
                  let uu____65347 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65347  in
                FStar_Syntax_Syntax.as_arg uu____65346  in
              [uu____65337]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____65336
             in
          uu____65331 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____65367 =
            let uu____65372 =
              let uu____65373 =
                let uu____65382 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____65382  in
              let uu____65383 =
                let uu____65394 =
                  let uu____65403 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____65403  in
                [uu____65394]  in
              uu____65373 :: uu____65383  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____65372
             in
          uu____65367 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_65428 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_65428.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_65428.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65449 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65449 with
    | (hd1,args) ->
        let uu____65494 =
          let uu____65507 =
            let uu____65508 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65508.FStar_Syntax_Syntax.n  in
          (uu____65507, args)  in
        (match uu____65494 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65538)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____65563 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65563
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65570  -> FStar_Pervasives_Native.Some _65570)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____65573)::(e2,uu____65575)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____65610 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____65610
               (fun e11  ->
                  let uu____65616 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____65616
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _65623  -> FStar_Pervasives_Native.Some _65623)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____65624 ->
             (if w
              then
                (let uu____65639 =
                   let uu____65645 =
                     let uu____65647 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____65647
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65645)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65639)
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
    let uu____65671 =
      let uu____65676 =
        let uu____65677 =
          let uu____65686 =
            let uu____65687 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____65687  in
          FStar_Syntax_Syntax.as_arg uu____65686  in
        [uu____65677]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____65676
       in
    uu____65671 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65711 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____65711 with
    | (bv,aq) ->
        let uu____65718 =
          let uu____65723 =
            let uu____65724 =
              let uu____65733 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____65733  in
            let uu____65734 =
              let uu____65745 =
                let uu____65754 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____65754  in
              [uu____65745]  in
            uu____65724 :: uu____65734  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____65723
           in
        uu____65718 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65786 =
      let uu____65791 =
        let uu____65792 =
          let uu____65801 =
            let uu____65802 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____65809 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____65802 i.FStar_Syntax_Syntax.rng uu____65809  in
          FStar_Syntax_Syntax.as_arg uu____65801  in
        [uu____65792]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____65791
       in
    uu____65786 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65839 =
      let uu____65844 =
        let uu____65845 =
          let uu____65854 =
            let uu____65855 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____65855  in
          FStar_Syntax_Syntax.as_arg uu____65854  in
        [uu____65845]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____65844
       in
    uu____65839 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65885 =
      let uu____65890 =
        let uu____65891 =
          let uu____65900 =
            let uu____65901 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____65901  in
          FStar_Syntax_Syntax.as_arg uu____65900  in
        [uu____65891]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____65890
       in
    uu____65885 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  