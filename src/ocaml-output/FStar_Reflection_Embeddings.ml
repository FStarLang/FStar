open Prims
let mk_emb :
  'Auu____64167 .
    (FStar_Range.range -> 'Auu____64167 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____64167 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____64167 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____64211 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____64211
  
let embed :
  'Auu____64259 .
    'Auu____64259 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____64259 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____64279 = FStar_Syntax_Embeddings.embed e x  in
        uu____64279 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____64320 .
    Prims.bool ->
      'Auu____64320 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____64320 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____64344 = FStar_Syntax_Embeddings.unembed e x  in
        uu____64344 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____64386 =
      let uu____64387 = FStar_Syntax_Subst.compress t  in
      uu____64387.FStar_Syntax_Syntax.n  in
    match uu____64386 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____64393;
          FStar_Syntax_Syntax.rng = uu____64394;_}
        ->
        let uu____64397 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64397
    | uu____64398 ->
        (if w
         then
           (let uu____64401 =
              let uu____64407 =
                let uu____64409 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____64409  in
              (FStar_Errors.Warning_NotEmbedded, uu____64407)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64401)
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
    let uu____64446 =
      let uu____64447 = FStar_Syntax_Subst.compress t  in
      uu____64447.FStar_Syntax_Syntax.n  in
    match uu____64446 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____64453;
          FStar_Syntax_Syntax.rng = uu____64454;_}
        ->
        let uu____64457 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64457
    | uu____64458 ->
        (if w
         then
           (let uu____64461 =
              let uu____64467 =
                let uu____64469 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____64469
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64467)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64461)
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
          let uu____64521 = f x  in
          FStar_Util.bind_opt uu____64521
            (fun x1  ->
               let uu____64529 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64529
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
        let uu____64598 =
          mapM_opt
            (fun uu____64611  ->
               match uu____64611 with
               | (bv,e) ->
                   let uu____64620 = unembed_term w e  in
                   FStar_Util.bind_opt uu____64620
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____64598
          (fun s  ->
             let uu____64634 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____64634)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____64636 =
        let uu____64637 = FStar_Syntax_Subst.compress t1  in
        uu____64637.FStar_Syntax_Syntax.n  in
      match uu____64636 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____64648 ->
          (if w
           then
             (let uu____64651 =
                let uu____64657 =
                  let uu____64659 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____64659
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____64657)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____64651)
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
          let uu____64694 =
            let uu____64699 =
              let uu____64700 =
                let uu____64709 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____64709  in
              [uu____64700]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____64699
             in
          uu____64694 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_64728 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_64728.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_64728.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64749 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64749 with
    | (hd1,args) ->
        let uu____64794 =
          let uu____64809 =
            let uu____64810 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64810.FStar_Syntax_Syntax.n  in
          (uu____64809, args)  in
        (match uu____64794 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____64865)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____64900 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____64900
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____64905 ->
             (if w
              then
                (let uu____64922 =
                   let uu____64928 =
                     let uu____64930 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____64930
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64928)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64922)
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
    let uu____64970 =
      let uu____64971 = FStar_Syntax_Subst.compress t  in
      uu____64971.FStar_Syntax_Syntax.n  in
    match uu____64970 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____64977;
          FStar_Syntax_Syntax.rng = uu____64978;_}
        ->
        let uu____64981 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64981
    | uu____64982 ->
        (if w
         then
           (let uu____64985 =
              let uu____64991 =
                let uu____64993 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____64993  in
              (FStar_Errors.Warning_NotEmbedded, uu____64991)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64985)
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
    let uu____65030 =
      let uu____65031 = FStar_Syntax_Subst.compress t  in
      uu____65031.FStar_Syntax_Syntax.n  in
    match uu____65030 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____65037;
          FStar_Syntax_Syntax.rng = uu____65038;_}
        ->
        let uu____65041 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65041
    | uu____65042 ->
        (if w
         then
           (let uu____65045 =
              let uu____65051 =
                let uu____65053 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____65053  in
              (FStar_Errors.Warning_NotEmbedded, uu____65051)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65045)
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
    let uu____65090 =
      let uu____65091 = FStar_Syntax_Subst.compress t  in
      uu____65091.FStar_Syntax_Syntax.n  in
    match uu____65090 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____65097;
          FStar_Syntax_Syntax.rng = uu____65098;_}
        ->
        let uu____65101 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65101
    | uu____65102 ->
        (if w
         then
           (let uu____65105 =
              let uu____65111 =
                let uu____65113 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____65113  in
              (FStar_Errors.Warning_NotEmbedded, uu____65111)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65105)
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
          let uu____65139 =
            let uu____65144 =
              let uu____65145 =
                let uu____65154 =
                  let uu____65155 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65155  in
                FStar_Syntax_Syntax.as_arg uu____65154  in
              [uu____65145]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____65144
             in
          uu____65139 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____65177 =
            let uu____65182 =
              let uu____65183 =
                let uu____65192 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____65192  in
              [uu____65183]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____65182
             in
          uu____65177 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____65213 =
            let uu____65218 =
              let uu____65219 =
                let uu____65228 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____65228  in
              [uu____65219]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____65218
             in
          uu____65213 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____65248 =
            let uu____65253 =
              let uu____65254 =
                let uu____65263 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____65263  in
              [uu____65254]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____65253
             in
          uu____65248 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_65285 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_65285.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_65285.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65306 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65306 with
    | (hd1,args) ->
        let uu____65351 =
          let uu____65366 =
            let uu____65367 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65367.FStar_Syntax_Syntax.n  in
          (uu____65366, args)  in
        (match uu____65351 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65441)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____65476 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65476
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65483  -> FStar_Pervasives_Native.Some _65483)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____65486)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____65521 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____65521
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _65532  -> FStar_Pervasives_Native.Some _65532)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____65535)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____65570 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____65570
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _65577  -> FStar_Pervasives_Native.Some _65577)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _65599  -> FStar_Pervasives_Native.Some _65599)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____65602)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____65637 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____65637
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _65656  -> FStar_Pervasives_Native.Some _65656)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____65657 ->
             (if w
              then
                (let uu____65674 =
                   let uu____65680 =
                     let uu____65682 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____65682
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65680)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65674)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____65695  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65708 =
            let uu____65713 =
              let uu____65714 =
                let uu____65723 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____65723  in
              [uu____65714]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____65713
             in
          uu____65708 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65748 =
            let uu____65753 =
              let uu____65754 =
                let uu____65763 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____65763  in
              let uu____65764 =
                let uu____65775 =
                  let uu____65784 =
                    let uu____65785 =
                      let uu____65790 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____65790  in
                    embed uu____65785 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____65784  in
                [uu____65775]  in
              uu____65754 :: uu____65764  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____65753
             in
          uu____65748 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65822 =
            let uu____65827 =
              let uu____65828 =
                let uu____65837 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65837  in
              [uu____65828]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____65827
             in
          uu____65822 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65857 =
            let uu____65862 =
              let uu____65863 =
                let uu____65872 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65872  in
              [uu____65863]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____65862
             in
          uu____65857 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65893 =
            let uu____65898 =
              let uu____65899 =
                let uu____65908 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65908  in
              let uu____65909 =
                let uu____65920 =
                  let uu____65929 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____65929  in
                [uu____65920]  in
              uu____65899 :: uu____65909  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____65898
             in
          uu____65893 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____65974 = FStar_Syntax_Util.head_and_args t1  in
      match uu____65974 with
      | (hd1,args) ->
          let uu____66019 =
            let uu____66032 =
              let uu____66033 = FStar_Syntax_Util.un_uinst hd1  in
              uu____66033.FStar_Syntax_Syntax.n  in
            (uu____66032, args)  in
          (match uu____66019 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____66048)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____66073 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____66073
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _66080  -> FStar_Pervasives_Native.Some _66080)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____66083)::(ps,uu____66085)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____66120 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____66120
                 (fun f1  ->
                    let uu____66126 =
                      let uu____66131 =
                        let uu____66136 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____66136  in
                      unembed' w uu____66131 ps  in
                    FStar_Util.bind_opt uu____66126
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _66149  ->
                              FStar_Pervasives_Native.Some _66149)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66154)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____66179 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66179
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66186  -> FStar_Pervasives_Native.Some _66186)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66189)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____66214 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66214
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66221  -> FStar_Pervasives_Native.Some _66221)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____66224)::(t2,uu____66226)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____66261 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66261
                 (fun bv1  ->
                    let uu____66267 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____66267
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _66274  ->
                              FStar_Pervasives_Native.Some _66274)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____66275 ->
               (if w
                then
                  (let uu____66290 =
                     let uu____66296 =
                       let uu____66298 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____66298
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____66296)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____66290)
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
    let uu____66325 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____66325
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____66340 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____66340 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____66363 =
            let uu____66368 =
              let uu____66369 =
                let uu____66378 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66378  in
              [uu____66369]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____66368
             in
          uu____66363 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____66398 =
            let uu____66403 =
              let uu____66404 =
                let uu____66413 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66413  in
              [uu____66404]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____66403
             in
          uu____66398 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____66433 =
            let uu____66438 =
              let uu____66439 =
                let uu____66448 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66448  in
              [uu____66439]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____66438
             in
          uu____66433 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66469 =
            let uu____66474 =
              let uu____66475 =
                let uu____66484 =
                  let uu____66485 = e_term_aq aq  in
                  embed uu____66485 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____66484  in
              let uu____66488 =
                let uu____66499 =
                  let uu____66508 =
                    let uu____66509 = e_argv_aq aq  in
                    embed uu____66509 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____66508  in
                [uu____66499]  in
              uu____66475 :: uu____66488  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____66474
             in
          uu____66469 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____66548 =
            let uu____66553 =
              let uu____66554 =
                let uu____66563 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66563  in
              let uu____66564 =
                let uu____66575 =
                  let uu____66584 =
                    let uu____66585 = e_term_aq aq  in
                    embed uu____66585 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66584  in
                [uu____66575]  in
              uu____66554 :: uu____66564  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____66553
             in
          uu____66548 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66616 =
            let uu____66621 =
              let uu____66622 =
                let uu____66631 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66631  in
              let uu____66632 =
                let uu____66643 =
                  let uu____66652 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____66652  in
                [uu____66643]  in
              uu____66622 :: uu____66632  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____66621
             in
          uu____66616 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66680 =
            let uu____66685 =
              let uu____66686 =
                let uu____66695 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____66695  in
              [uu____66686]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____66685
             in
          uu____66680 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____66716 =
            let uu____66721 =
              let uu____66722 =
                let uu____66731 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66731  in
              let uu____66732 =
                let uu____66743 =
                  let uu____66752 =
                    let uu____66753 = e_term_aq aq  in
                    embed uu____66753 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66752  in
                [uu____66743]  in
              uu____66722 :: uu____66732  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____66721
             in
          uu____66716 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66783 =
            let uu____66788 =
              let uu____66789 =
                let uu____66798 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____66798  in
              [uu____66789]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____66788
             in
          uu____66783 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66819 =
            let uu____66824 =
              let uu____66825 =
                let uu____66834 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____66834  in
              let uu____66835 =
                let uu____66846 =
                  let uu____66855 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____66855  in
                [uu____66846]  in
              uu____66825 :: uu____66835  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____66824
             in
          uu____66819 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66892 =
            let uu____66897 =
              let uu____66898 =
                let uu____66907 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____66907  in
              let uu____66909 =
                let uu____66920 =
                  let uu____66929 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____66929  in
                let uu____66930 =
                  let uu____66941 =
                    let uu____66950 =
                      let uu____66951 = e_term_aq aq  in
                      embed uu____66951 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____66950  in
                  let uu____66954 =
                    let uu____66965 =
                      let uu____66974 =
                        let uu____66975 = e_term_aq aq  in
                        embed uu____66975 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____66974  in
                    [uu____66965]  in
                  uu____66941 :: uu____66954  in
                uu____66920 :: uu____66930  in
              uu____66898 :: uu____66909  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____66897
             in
          uu____66892 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____67026 =
            let uu____67031 =
              let uu____67032 =
                let uu____67041 =
                  let uu____67042 = e_term_aq aq  in embed uu____67042 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____67041  in
              let uu____67045 =
                let uu____67056 =
                  let uu____67065 =
                    let uu____67066 =
                      let uu____67075 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____67075  in
                    embed uu____67066 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____67065  in
                [uu____67056]  in
              uu____67032 :: uu____67045  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____67031
             in
          uu____67026 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____67125 =
            let uu____67130 =
              let uu____67131 =
                let uu____67140 =
                  let uu____67141 = e_term_aq aq  in embed uu____67141 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67140  in
              let uu____67144 =
                let uu____67155 =
                  let uu____67164 =
                    let uu____67165 = e_term_aq aq  in
                    embed uu____67165 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____67164  in
                let uu____67168 =
                  let uu____67179 =
                    let uu____67188 =
                      let uu____67189 =
                        let uu____67194 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67194  in
                      embed uu____67189 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67188  in
                  [uu____67179]  in
                uu____67155 :: uu____67168  in
              uu____67131 :: uu____67144  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____67130
             in
          uu____67125 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____67240 =
            let uu____67245 =
              let uu____67246 =
                let uu____67255 =
                  let uu____67256 = e_term_aq aq  in embed uu____67256 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67255  in
              let uu____67259 =
                let uu____67270 =
                  let uu____67279 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____67279  in
                let uu____67280 =
                  let uu____67291 =
                    let uu____67300 =
                      let uu____67301 =
                        let uu____67306 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67306  in
                      embed uu____67301 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67300  in
                  [uu____67291]  in
                uu____67270 :: uu____67280  in
              uu____67246 :: uu____67259  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____67245
             in
          uu____67240 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_67345 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_67345.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_67345.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____67363 = FStar_Syntax_Util.head_and_args t  in
      match uu____67363 with
      | (hd1,args) ->
          let uu____67408 =
            let uu____67421 =
              let uu____67422 = FStar_Syntax_Util.un_uinst hd1  in
              uu____67422.FStar_Syntax_Syntax.n  in
            (uu____67421, args)  in
          (match uu____67408 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67437)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____67462 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67462
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67469  -> FStar_Pervasives_Native.Some _67469)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67472)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____67497 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67497
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67504  -> FStar_Pervasives_Native.Some _67504)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____67507)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____67532 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____67532
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _67539  -> FStar_Pervasives_Native.Some _67539)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____67542)::(r,uu____67544)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____67579 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____67579
                 (fun l1  ->
                    let uu____67585 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____67585
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _67592  ->
                              FStar_Pervasives_Native.Some _67592)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67595)::(t1,uu____67597)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____67632 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67632
                 (fun b1  ->
                    let uu____67638 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67638
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67645  ->
                              FStar_Pervasives_Native.Some _67645)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67648)::(t1,uu____67650)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____67685 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67685
                 (fun b1  ->
                    let uu____67691 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____67691
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _67698  ->
                              FStar_Pervasives_Native.Some _67698)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____67701)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____67726 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____67726
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _67733  -> FStar_Pervasives_Native.Some _67733)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67736)::(t1,uu____67738)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____67773 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67773
                 (fun b1  ->
                    let uu____67779 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67779
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67786  ->
                              FStar_Pervasives_Native.Some _67786)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____67789)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____67814 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____67814
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _67821  -> FStar_Pervasives_Native.Some _67821)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____67824)::(l,uu____67826)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____67861 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____67861
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _67870  -> FStar_Pervasives_Native.Some _67870)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____67873)::(b,uu____67875)::(t1,uu____67877)::
              (t2,uu____67879)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____67934 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____67934
                 (fun r1  ->
                    let uu____67944 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____67944
                      (fun b1  ->
                         let uu____67950 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____67950
                           (fun t11  ->
                              let uu____67956 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____67956
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _67963  ->
                                        FStar_Pervasives_Native.Some _67963)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____67967)::(brs,uu____67969)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____68004 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____68004
                 (fun t2  ->
                    let uu____68010 =
                      let uu____68015 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____68015 brs  in
                    FStar_Util.bind_opt uu____68010
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _68030  ->
                              FStar_Pervasives_Native.Some _68030)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68035)::(t1,uu____68037)::(tacopt,uu____68039)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____68084 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68084
                 (fun e1  ->
                    let uu____68090 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____68090
                      (fun t2  ->
                         let uu____68096 =
                           let uu____68101 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68101 tacopt  in
                         FStar_Util.bind_opt uu____68096
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68116  ->
                                   FStar_Pervasives_Native.Some _68116)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68121)::(c,uu____68123)::(tacopt,uu____68125)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____68170 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68170
                 (fun e1  ->
                    let uu____68176 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____68176
                      (fun c1  ->
                         let uu____68182 =
                           let uu____68187 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68187 tacopt  in
                         FStar_Util.bind_opt uu____68182
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68202  ->
                                   FStar_Pervasives_Native.Some _68202)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _68222  -> FStar_Pervasives_Native.Some _68222)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____68223 ->
               (if w
                then
                  (let uu____68238 =
                     let uu____68244 =
                       let uu____68246 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____68246
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____68244)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____68238)
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
    let uu____68275 =
      let uu____68280 =
        let uu____68281 =
          let uu____68290 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____68290  in
        let uu____68292 =
          let uu____68303 =
            let uu____68312 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____68312  in
          let uu____68313 =
            let uu____68324 =
              let uu____68333 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____68333  in
            [uu____68324]  in
          uu____68303 :: uu____68313  in
        uu____68281 :: uu____68292  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____68280
       in
    uu____68275 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68386 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68386 with
    | (hd1,args) ->
        let uu____68431 =
          let uu____68444 =
            let uu____68445 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68445.FStar_Syntax_Syntax.n  in
          (uu____68444, args)  in
        (match uu____68431 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____68460)::(idx,uu____68462)::(s,uu____68464)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____68509 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____68509
               (fun nm1  ->
                  let uu____68519 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____68519
                    (fun idx1  ->
                       let uu____68525 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____68525
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _68532  ->
                                 FStar_Pervasives_Native.Some _68532)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____68533 ->
             (if w
              then
                (let uu____68548 =
                   let uu____68554 =
                     let uu____68556 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____68556
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____68554)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____68548)
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
        let uu____68582 =
          let uu____68587 =
            let uu____68588 =
              let uu____68597 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____68597  in
            let uu____68598 =
              let uu____68609 =
                let uu____68618 =
                  let uu____68619 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____68619 rng md  in
                FStar_Syntax_Syntax.as_arg uu____68618  in
              [uu____68609]  in
            uu____68588 :: uu____68598  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____68587
           in
        uu____68582 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____68657 =
          let uu____68662 =
            let uu____68663 =
              let uu____68672 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____68672  in
            let uu____68673 =
              let uu____68684 =
                let uu____68693 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____68693  in
              [uu____68684]  in
            uu____68663 :: uu____68673  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____68662
           in
        uu____68657 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_68720 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_68720.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_68720.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68739 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68739 with
    | (hd1,args) ->
        let uu____68784 =
          let uu____68797 =
            let uu____68798 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68798.FStar_Syntax_Syntax.n  in
          (uu____68797, args)  in
        (match uu____68784 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____68813)::(md,uu____68815)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____68850 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____68850
               (fun t3  ->
                  let uu____68856 =
                    let uu____68861 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____68861 md  in
                  FStar_Util.bind_opt uu____68856
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _68876  -> FStar_Pervasives_Native.Some _68876)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____68881)::(post,uu____68883)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____68918 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____68918
               (fun pre1  ->
                  let uu____68924 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____68924
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _68931  -> FStar_Pervasives_Native.Some _68931)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _68949  -> FStar_Pervasives_Native.Some _68949)
               FStar_Reflection_Data.C_Unknown
         | uu____68950 ->
             (if w
              then
                (let uu____68965 =
                   let uu____68971 =
                     let uu____68973 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____68973
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____68971)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____68965)
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
    let uu___1175_68998 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_68998.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_68998.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69019 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69019 with
    | (hd1,args) ->
        let uu____69064 =
          let uu____69079 =
            let uu____69080 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69080.FStar_Syntax_Syntax.n  in
          (uu____69079, args)  in
        (match uu____69064 with
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
         | uu____69152 ->
             (if w
              then
                (let uu____69169 =
                   let uu____69175 =
                     let uu____69177 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____69177
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69175)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69169)
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
    let uu____69214 =
      let uu____69215 = FStar_Syntax_Subst.compress t  in
      uu____69215.FStar_Syntax_Syntax.n  in
    match uu____69214 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____69221;
          FStar_Syntax_Syntax.rng = uu____69222;_}
        ->
        let uu____69225 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____69225
    | uu____69226 ->
        (if w
         then
           (let uu____69229 =
              let uu____69235 =
                let uu____69237 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____69237
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____69235)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69229)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____69297 uu____69298 =
    let uu____69320 =
      let uu____69326 = FStar_Ident.range_of_id i  in
      let uu____69327 = FStar_Ident.text_of_id i  in
      (uu____69326, uu____69327)  in
    embed repr rng uu____69320  in
  let unembed_ident t w uu____69355 =
    let uu____69361 = unembed' w repr t  in
    match uu____69361 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____69385 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____69385
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____69392 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____69392
  
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
        let uu____69431 =
          let uu____69436 =
            let uu____69437 =
              let uu____69446 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____69446  in
            let uu____69448 =
              let uu____69459 =
                let uu____69468 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____69468  in
              let uu____69469 =
                let uu____69480 =
                  let uu____69489 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____69489  in
                let uu____69492 =
                  let uu____69503 =
                    let uu____69512 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____69512  in
                  let uu____69513 =
                    let uu____69524 =
                      let uu____69533 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____69533  in
                    [uu____69524]  in
                  uu____69503 :: uu____69513  in
                uu____69480 :: uu____69492  in
              uu____69459 :: uu____69469  in
            uu____69437 :: uu____69448  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____69436
           in
        uu____69431 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____69586 =
          let uu____69591 =
            let uu____69592 =
              let uu____69601 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69601  in
            let uu____69605 =
              let uu____69616 =
                let uu____69625 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____69625  in
              [uu____69616]  in
            uu____69592 :: uu____69605  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____69591
           in
        uu____69586 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____69669 =
          let uu____69674 =
            let uu____69675 =
              let uu____69684 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69684  in
            let uu____69688 =
              let uu____69699 =
                let uu____69708 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____69708  in
              let uu____69711 =
                let uu____69722 =
                  let uu____69731 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____69731  in
                let uu____69732 =
                  let uu____69743 =
                    let uu____69752 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____69752  in
                  let uu____69753 =
                    let uu____69764 =
                      let uu____69773 =
                        let uu____69774 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____69774 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____69773  in
                    [uu____69764]  in
                  uu____69743 :: uu____69753  in
                uu____69722 :: uu____69732  in
              uu____69699 :: uu____69711  in
            uu____69675 :: uu____69688  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____69674
           in
        uu____69669 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_69840 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_69840.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_69840.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69859 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69859 with
    | (hd1,args) ->
        let uu____69904 =
          let uu____69917 =
            let uu____69918 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69918.FStar_Syntax_Syntax.n  in
          (uu____69917, args)  in
        (match uu____69904 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____69933)::(us,uu____69935)::(bs,uu____69937)::
            (t2,uu____69939)::(dcs,uu____69941)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____70006 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____70006
               (fun nm1  ->
                  let uu____70024 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____70024
                    (fun us1  ->
                       let uu____70038 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____70038
                         (fun bs1  ->
                            let uu____70044 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____70044
                              (fun t3  ->
                                 let uu____70050 =
                                   let uu____70058 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____70058 dcs  in
                                 FStar_Util.bind_opt uu____70050
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _70088  ->
                                           FStar_Pervasives_Native.Some
                                             _70088)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____70097)::(fvar1,uu____70099)::(univs1,uu____70101)::
            (ty,uu____70103)::(t2,uu____70105)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____70170 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____70170
               (fun r1  ->
                  let uu____70180 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____70180
                    (fun fvar2  ->
                       let uu____70186 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____70186
                         (fun univs2  ->
                            let uu____70200 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____70200
                              (fun ty1  ->
                                 let uu____70206 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____70206
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _70213  ->
                                           FStar_Pervasives_Native.Some
                                             _70213)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____70232 ->
             (if w
              then
                (let uu____70247 =
                   let uu____70253 =
                     let uu____70255 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____70255
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70253)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70247)
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
          let uu____70281 =
            let uu____70286 =
              let uu____70287 =
                let uu____70296 =
                  let uu____70297 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____70297  in
                FStar_Syntax_Syntax.as_arg uu____70296  in
              [uu____70287]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____70286
             in
          uu____70281 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____70319 =
            let uu____70324 =
              let uu____70325 =
                let uu____70334 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____70334  in
              let uu____70335 =
                let uu____70346 =
                  let uu____70355 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____70355  in
                [uu____70346]  in
              uu____70325 :: uu____70335  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____70324
             in
          uu____70319 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_70382 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_70382.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_70382.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____70403 = FStar_Syntax_Util.head_and_args t1  in
    match uu____70403 with
    | (hd1,args) ->
        let uu____70448 =
          let uu____70461 =
            let uu____70462 = FStar_Syntax_Util.un_uinst hd1  in
            uu____70462.FStar_Syntax_Syntax.n  in
          (uu____70461, args)  in
        (match uu____70448 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____70492)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____70517 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____70517
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _70524  -> FStar_Pervasives_Native.Some _70524)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____70527)::(e2,uu____70529)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____70564 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____70564
               (fun e11  ->
                  let uu____70570 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____70570
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _70577  -> FStar_Pervasives_Native.Some _70577)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____70578 ->
             (if w
              then
                (let uu____70593 =
                   let uu____70599 =
                     let uu____70601 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____70601
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70599)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70593)
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
    let uu____70625 =
      let uu____70630 =
        let uu____70631 =
          let uu____70640 =
            let uu____70641 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____70641  in
          FStar_Syntax_Syntax.as_arg uu____70640  in
        [uu____70631]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____70630
       in
    uu____70625 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70667 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____70667 with
    | (bv,aq) ->
        let uu____70674 =
          let uu____70679 =
            let uu____70680 =
              let uu____70689 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____70689  in
            let uu____70690 =
              let uu____70701 =
                let uu____70710 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____70710  in
              [uu____70701]  in
            uu____70680 :: uu____70690  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____70679
           in
        uu____70674 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70744 =
      let uu____70749 =
        let uu____70750 =
          let uu____70759 =
            let uu____70760 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____70767 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____70760 i.FStar_Syntax_Syntax.rng uu____70767  in
          FStar_Syntax_Syntax.as_arg uu____70759  in
        [uu____70750]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____70749
       in
    uu____70744 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70799 =
      let uu____70804 =
        let uu____70805 =
          let uu____70814 =
            let uu____70815 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____70815  in
          FStar_Syntax_Syntax.as_arg uu____70814  in
        [uu____70805]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____70804
       in
    uu____70799 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70847 =
      let uu____70852 =
        let uu____70853 =
          let uu____70862 =
            let uu____70863 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____70863  in
          FStar_Syntax_Syntax.as_arg uu____70862  in
        [uu____70853]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____70852
       in
    uu____70847 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  