open Prims
let mk_emb :
  'Auu____59354 .
    (FStar_Range.range -> 'Auu____59354 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____59354 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____59354 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____59398 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____59398
  
let embed :
  'Auu____59425 .
    'Auu____59425 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____59425 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____59445 = FStar_Syntax_Embeddings.embed e x  in
        uu____59445 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____59463 .
    Prims.bool ->
      'Auu____59463 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____59463 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____59487 = FStar_Syntax_Embeddings.unembed e x  in
        uu____59487 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____59525 =
      let uu____59526 = FStar_Syntax_Subst.compress t  in
      uu____59526.FStar_Syntax_Syntax.n  in
    match uu____59525 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____59532;
          FStar_Syntax_Syntax.rng = uu____59533;_}
        ->
        let uu____59536 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59536
    | uu____59537 ->
        (if w
         then
           (let uu____59540 =
              let uu____59546 =
                let uu____59548 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____59548  in
              (FStar_Errors.Warning_NotEmbedded, uu____59546)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59540)
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
    let uu____59585 =
      let uu____59586 = FStar_Syntax_Subst.compress t  in
      uu____59586.FStar_Syntax_Syntax.n  in
    match uu____59585 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____59592;
          FStar_Syntax_Syntax.rng = uu____59593;_}
        ->
        let uu____59596 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59596
    | uu____59597 ->
        (if w
         then
           (let uu____59600 =
              let uu____59606 =
                let uu____59608 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____59608
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____59606)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59600)
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
          let uu____59660 = f x  in
          FStar_Util.bind_opt uu____59660
            (fun x1  ->
               let uu____59668 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59668
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
        let uu____59737 =
          mapM_opt
            (fun uu____59750  ->
               match uu____59750 with
               | (bv,e) ->
                   let uu____59759 = unembed_term w e  in
                   FStar_Util.bind_opt uu____59759
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____59737
          (fun s  ->
             let uu____59773 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____59773)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____59775 =
        let uu____59776 = FStar_Syntax_Subst.compress t1  in
        uu____59776.FStar_Syntax_Syntax.n  in
      match uu____59775 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____59787 ->
          (if w
           then
             (let uu____59790 =
                let uu____59796 =
                  let uu____59798 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____59798
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____59796)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____59790)
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
          let uu____59833 =
            let uu____59838 =
              let uu____59839 =
                let uu____59848 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____59848  in
              [uu____59839]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____59838
             in
          uu____59833 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_59865 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_59865.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_59865.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____59886 = FStar_Syntax_Util.head_and_args t1  in
    match uu____59886 with
    | (hd1,args) ->
        let uu____59931 =
          let uu____59946 =
            let uu____59947 = FStar_Syntax_Util.un_uinst hd1  in
            uu____59947.FStar_Syntax_Syntax.n  in
          (uu____59946, args)  in
        (match uu____59931 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____60002)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____60037 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____60037
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____60042 ->
             (if w
              then
                (let uu____60059 =
                   let uu____60065 =
                     let uu____60067 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____60067
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60065)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60059)
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
    let uu____60107 =
      let uu____60108 = FStar_Syntax_Subst.compress t  in
      uu____60108.FStar_Syntax_Syntax.n  in
    match uu____60107 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____60114;
          FStar_Syntax_Syntax.rng = uu____60115;_}
        ->
        let uu____60118 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60118
    | uu____60119 ->
        (if w
         then
           (let uu____60122 =
              let uu____60128 =
                let uu____60130 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____60130  in
              (FStar_Errors.Warning_NotEmbedded, uu____60128)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60122)
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
    let uu____60167 =
      let uu____60168 = FStar_Syntax_Subst.compress t  in
      uu____60168.FStar_Syntax_Syntax.n  in
    match uu____60167 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____60174;
          FStar_Syntax_Syntax.rng = uu____60175;_}
        ->
        let uu____60178 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60178
    | uu____60179 ->
        (if w
         then
           (let uu____60182 =
              let uu____60188 =
                let uu____60190 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____60190  in
              (FStar_Errors.Warning_NotEmbedded, uu____60188)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60182)
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
    let uu____60227 =
      let uu____60228 = FStar_Syntax_Subst.compress t  in
      uu____60228.FStar_Syntax_Syntax.n  in
    match uu____60227 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____60234;
          FStar_Syntax_Syntax.rng = uu____60235;_}
        ->
        let uu____60238 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60238
    | uu____60239 ->
        (if w
         then
           (let uu____60242 =
              let uu____60248 =
                let uu____60250 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____60250  in
              (FStar_Errors.Warning_NotEmbedded, uu____60248)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60242)
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
          let uu____60276 =
            let uu____60281 =
              let uu____60282 =
                let uu____60291 =
                  let uu____60292 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____60292  in
                FStar_Syntax_Syntax.as_arg uu____60291  in
              [uu____60282]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____60281
             in
          uu____60276 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____60312 =
            let uu____60317 =
              let uu____60318 =
                let uu____60327 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____60327  in
              [uu____60318]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____60317
             in
          uu____60312 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____60346 =
            let uu____60351 =
              let uu____60352 =
                let uu____60361 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____60361  in
              [uu____60352]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____60351
             in
          uu____60346 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____60379 =
            let uu____60384 =
              let uu____60385 =
                let uu____60394 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____60394  in
              [uu____60385]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____60384
             in
          uu____60379 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_60414 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_60414.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_60414.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____60435 = FStar_Syntax_Util.head_and_args t1  in
    match uu____60435 with
    | (hd1,args) ->
        let uu____60480 =
          let uu____60495 =
            let uu____60496 = FStar_Syntax_Util.un_uinst hd1  in
            uu____60496.FStar_Syntax_Syntax.n  in
          (uu____60495, args)  in
        (match uu____60480 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____60570)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____60605 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____60605
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _60612  -> FStar_Pervasives_Native.Some _60612)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____60615)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____60650 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____60650
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _60661  -> FStar_Pervasives_Native.Some _60661)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____60664)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____60699 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____60699
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _60706  -> FStar_Pervasives_Native.Some _60706)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _60728  -> FStar_Pervasives_Native.Some _60728)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____60731)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____60766 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____60766
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _60785  -> FStar_Pervasives_Native.Some _60785)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____60786 ->
             (if w
              then
                (let uu____60803 =
                   let uu____60809 =
                     let uu____60811 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____60811
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60809)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60803)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____60824  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60837 =
            let uu____60842 =
              let uu____60843 =
                let uu____60852 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____60852  in
              [uu____60843]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____60842
             in
          uu____60837 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60875 =
            let uu____60880 =
              let uu____60881 =
                let uu____60890 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____60890  in
              let uu____60891 =
                let uu____60902 =
                  let uu____60911 =
                    let uu____60912 =
                      let uu____60917 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____60917  in
                    embed uu____60912 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____60911  in
                [uu____60902]  in
              uu____60881 :: uu____60891  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____60880
             in
          uu____60875 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60947 =
            let uu____60952 =
              let uu____60953 =
                let uu____60962 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____60962  in
              [uu____60953]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____60952
             in
          uu____60947 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____60980 =
            let uu____60985 =
              let uu____60986 =
                let uu____60995 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____60995  in
              [uu____60986]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____60985
             in
          uu____60980 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____61014 =
            let uu____61019 =
              let uu____61020 =
                let uu____61029 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61029  in
              let uu____61030 =
                let uu____61041 =
                  let uu____61050 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____61050  in
                [uu____61041]  in
              uu____61020 :: uu____61030  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____61019
             in
          uu____61014 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____61093 = FStar_Syntax_Util.head_and_args t1  in
      match uu____61093 with
      | (hd1,args) ->
          let uu____61138 =
            let uu____61151 =
              let uu____61152 = FStar_Syntax_Util.un_uinst hd1  in
              uu____61152.FStar_Syntax_Syntax.n  in
            (uu____61151, args)  in
          (match uu____61138 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____61167)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____61192 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____61192
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _61199  -> FStar_Pervasives_Native.Some _61199)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____61202)::(ps,uu____61204)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____61239 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____61239
                 (fun f1  ->
                    let uu____61245 =
                      let uu____61250 =
                        let uu____61255 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____61255  in
                      unembed' w uu____61250 ps  in
                    FStar_Util.bind_opt uu____61245
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _61268  ->
                              FStar_Pervasives_Native.Some _61268)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61273)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____61298 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61298
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61305  -> FStar_Pervasives_Native.Some _61305)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61308)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____61333 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61333
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61340  -> FStar_Pervasives_Native.Some _61340)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____61343)::(t2,uu____61345)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____61380 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61380
                 (fun bv1  ->
                    let uu____61386 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____61386
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _61393  ->
                              FStar_Pervasives_Native.Some _61393)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____61394 ->
               (if w
                then
                  (let uu____61409 =
                     let uu____61415 =
                       let uu____61417 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____61417
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____61415)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____61409)
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
    let uu____61444 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____61444
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____61459 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____61459 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61482 =
            let uu____61487 =
              let uu____61488 =
                let uu____61497 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61497  in
              [uu____61488]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____61487
             in
          uu____61482 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____61515 =
            let uu____61520 =
              let uu____61521 =
                let uu____61530 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61530  in
              [uu____61521]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____61520
             in
          uu____61515 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61548 =
            let uu____61553 =
              let uu____61554 =
                let uu____61563 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61563  in
              [uu____61554]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____61553
             in
          uu____61548 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61582 =
            let uu____61587 =
              let uu____61588 =
                let uu____61597 =
                  let uu____61598 = e_term_aq aq  in
                  embed uu____61598 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____61597  in
              let uu____61601 =
                let uu____61612 =
                  let uu____61621 =
                    let uu____61622 = e_argv_aq aq  in
                    embed uu____61622 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____61621  in
                [uu____61612]  in
              uu____61588 :: uu____61601  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____61587
             in
          uu____61582 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____61659 =
            let uu____61664 =
              let uu____61665 =
                let uu____61674 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61674  in
              let uu____61675 =
                let uu____61686 =
                  let uu____61695 =
                    let uu____61696 = e_term_aq aq  in
                    embed uu____61696 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61695  in
                [uu____61686]  in
              uu____61665 :: uu____61675  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____61664
             in
          uu____61659 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61725 =
            let uu____61730 =
              let uu____61731 =
                let uu____61740 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61740  in
              let uu____61741 =
                let uu____61752 =
                  let uu____61761 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____61761  in
                [uu____61752]  in
              uu____61731 :: uu____61741  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____61730
             in
          uu____61725 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61787 =
            let uu____61792 =
              let uu____61793 =
                let uu____61802 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____61802  in
              [uu____61793]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____61792
             in
          uu____61787 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____61821 =
            let uu____61826 =
              let uu____61827 =
                let uu____61836 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61836  in
              let uu____61837 =
                let uu____61848 =
                  let uu____61857 =
                    let uu____61858 = e_term_aq aq  in
                    embed uu____61858 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61857  in
                [uu____61848]  in
              uu____61827 :: uu____61837  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____61826
             in
          uu____61821 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61886 =
            let uu____61891 =
              let uu____61892 =
                let uu____61901 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____61901  in
              [uu____61892]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____61891
             in
          uu____61886 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61920 =
            let uu____61925 =
              let uu____61926 =
                let uu____61935 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____61935  in
              let uu____61936 =
                let uu____61947 =
                  let uu____61956 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____61956  in
                [uu____61947]  in
              uu____61926 :: uu____61936  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____61925
             in
          uu____61920 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____61991 =
            let uu____61996 =
              let uu____61997 =
                let uu____62006 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____62006  in
              let uu____62008 =
                let uu____62019 =
                  let uu____62028 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____62028  in
                let uu____62029 =
                  let uu____62040 =
                    let uu____62049 =
                      let uu____62050 = e_term_aq aq  in
                      embed uu____62050 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____62049  in
                  let uu____62053 =
                    let uu____62064 =
                      let uu____62073 =
                        let uu____62074 = e_term_aq aq  in
                        embed uu____62074 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____62073  in
                    [uu____62064]  in
                  uu____62040 :: uu____62053  in
                uu____62019 :: uu____62029  in
              uu____61997 :: uu____62008  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____61996
             in
          uu____61991 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____62123 =
            let uu____62128 =
              let uu____62129 =
                let uu____62138 =
                  let uu____62139 = e_term_aq aq  in embed uu____62139 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____62138  in
              let uu____62142 =
                let uu____62153 =
                  let uu____62162 =
                    let uu____62163 =
                      let uu____62172 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____62172  in
                    embed uu____62163 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____62162  in
                [uu____62153]  in
              uu____62129 :: uu____62142  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____62128
             in
          uu____62123 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____62220 =
            let uu____62225 =
              let uu____62226 =
                let uu____62235 =
                  let uu____62236 = e_term_aq aq  in embed uu____62236 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62235  in
              let uu____62239 =
                let uu____62250 =
                  let uu____62259 =
                    let uu____62260 = e_term_aq aq  in
                    embed uu____62260 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____62259  in
                let uu____62263 =
                  let uu____62274 =
                    let uu____62283 =
                      let uu____62284 =
                        let uu____62289 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62289  in
                      embed uu____62284 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62283  in
                  [uu____62274]  in
                uu____62250 :: uu____62263  in
              uu____62226 :: uu____62239  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____62225
             in
          uu____62220 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____62333 =
            let uu____62338 =
              let uu____62339 =
                let uu____62348 =
                  let uu____62349 = e_term_aq aq  in embed uu____62349 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62348  in
              let uu____62352 =
                let uu____62363 =
                  let uu____62372 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____62372  in
                let uu____62373 =
                  let uu____62384 =
                    let uu____62393 =
                      let uu____62394 =
                        let uu____62399 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62399  in
                      embed uu____62394 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62393  in
                  [uu____62384]  in
                uu____62363 :: uu____62373  in
              uu____62339 :: uu____62352  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____62338
             in
          uu____62333 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_62436 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_62436.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_62436.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____62454 = FStar_Syntax_Util.head_and_args t  in
      match uu____62454 with
      | (hd1,args) ->
          let uu____62499 =
            let uu____62512 =
              let uu____62513 = FStar_Syntax_Util.un_uinst hd1  in
              uu____62513.FStar_Syntax_Syntax.n  in
            (uu____62512, args)  in
          (match uu____62499 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62528)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____62553 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62553
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62560  -> FStar_Pervasives_Native.Some _62560)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62563)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____62588 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62588
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62595  -> FStar_Pervasives_Native.Some _62595)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____62598)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____62623 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____62623
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _62630  -> FStar_Pervasives_Native.Some _62630)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____62633)::(r,uu____62635)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____62670 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____62670
                 (fun l1  ->
                    let uu____62676 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____62676
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _62683  ->
                              FStar_Pervasives_Native.Some _62683)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62686)::(t1,uu____62688)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____62723 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62723
                 (fun b1  ->
                    let uu____62729 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62729
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62736  ->
                              FStar_Pervasives_Native.Some _62736)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62739)::(t1,uu____62741)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____62776 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62776
                 (fun b1  ->
                    let uu____62782 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____62782
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _62789  ->
                              FStar_Pervasives_Native.Some _62789)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____62792)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____62817 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____62817
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _62824  -> FStar_Pervasives_Native.Some _62824)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62827)::(t1,uu____62829)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____62864 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62864
                 (fun b1  ->
                    let uu____62870 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62870
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62877  ->
                              FStar_Pervasives_Native.Some _62877)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____62880)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____62905 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____62905
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _62912  -> FStar_Pervasives_Native.Some _62912)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____62915)::(l,uu____62917)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____62952 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____62952
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _62961  -> FStar_Pervasives_Native.Some _62961)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____62964)::(b,uu____62966)::(t1,uu____62968)::
              (t2,uu____62970)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____63025 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____63025
                 (fun r1  ->
                    let uu____63035 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____63035
                      (fun b1  ->
                         let uu____63041 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____63041
                           (fun t11  ->
                              let uu____63047 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____63047
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _63054  ->
                                        FStar_Pervasives_Native.Some _63054)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____63058)::(brs,uu____63060)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____63095 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____63095
                 (fun t2  ->
                    let uu____63101 =
                      let uu____63106 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____63106 brs  in
                    FStar_Util.bind_opt uu____63101
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _63121  ->
                              FStar_Pervasives_Native.Some _63121)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63126)::(t1,uu____63128)::(tacopt,uu____63130)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____63175 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63175
                 (fun e1  ->
                    let uu____63181 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____63181
                      (fun t2  ->
                         let uu____63187 =
                           let uu____63192 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63192 tacopt  in
                         FStar_Util.bind_opt uu____63187
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63207  ->
                                   FStar_Pervasives_Native.Some _63207)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63212)::(c,uu____63214)::(tacopt,uu____63216)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____63261 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63261
                 (fun e1  ->
                    let uu____63267 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____63267
                      (fun c1  ->
                         let uu____63273 =
                           let uu____63278 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63278 tacopt  in
                         FStar_Util.bind_opt uu____63273
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63293  ->
                                   FStar_Pervasives_Native.Some _63293)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _63313  -> FStar_Pervasives_Native.Some _63313)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____63314 ->
               (if w
                then
                  (let uu____63329 =
                     let uu____63335 =
                       let uu____63337 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____63337
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____63335)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____63329)
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
    let uu____63366 =
      let uu____63371 =
        let uu____63372 =
          let uu____63381 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____63381  in
        let uu____63383 =
          let uu____63394 =
            let uu____63403 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____63403  in
          let uu____63404 =
            let uu____63415 =
              let uu____63424 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____63424  in
            [uu____63415]  in
          uu____63394 :: uu____63404  in
        uu____63372 :: uu____63383  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____63371
       in
    uu____63366 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63475 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63475 with
    | (hd1,args) ->
        let uu____63520 =
          let uu____63533 =
            let uu____63534 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63534.FStar_Syntax_Syntax.n  in
          (uu____63533, args)  in
        (match uu____63520 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____63549)::(idx,uu____63551)::(s,uu____63553)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____63598 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____63598
               (fun nm1  ->
                  let uu____63608 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____63608
                    (fun idx1  ->
                       let uu____63614 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____63614
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _63621  ->
                                 FStar_Pervasives_Native.Some _63621)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____63622 ->
             (if w
              then
                (let uu____63637 =
                   let uu____63643 =
                     let uu____63645 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____63645
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____63643)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____63637)
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
        let uu____63671 =
          let uu____63676 =
            let uu____63677 =
              let uu____63686 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____63686  in
            let uu____63687 =
              let uu____63698 =
                let uu____63707 =
                  let uu____63708 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____63708 rng md  in
                FStar_Syntax_Syntax.as_arg uu____63707  in
              [uu____63698]  in
            uu____63677 :: uu____63687  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____63676
           in
        uu____63671 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____63744 =
          let uu____63749 =
            let uu____63750 =
              let uu____63759 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____63759  in
            let uu____63760 =
              let uu____63771 =
                let uu____63780 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____63780  in
              [uu____63771]  in
            uu____63750 :: uu____63760  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____63749
           in
        uu____63744 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_63805 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_63805.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_63805.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63824 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63824 with
    | (hd1,args) ->
        let uu____63869 =
          let uu____63882 =
            let uu____63883 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63883.FStar_Syntax_Syntax.n  in
          (uu____63882, args)  in
        (match uu____63869 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____63898)::(md,uu____63900)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____63935 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____63935
               (fun t3  ->
                  let uu____63941 =
                    let uu____63946 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____63946 md  in
                  FStar_Util.bind_opt uu____63941
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _63961  -> FStar_Pervasives_Native.Some _63961)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____63966)::(post,uu____63968)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____64003 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____64003
               (fun pre1  ->
                  let uu____64009 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____64009
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _64016  -> FStar_Pervasives_Native.Some _64016)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _64034  -> FStar_Pervasives_Native.Some _64034)
               FStar_Reflection_Data.C_Unknown
         | uu____64035 ->
             (if w
              then
                (let uu____64050 =
                   let uu____64056 =
                     let uu____64058 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____64058
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64056)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64050)
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
    let uu___1175_64083 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_64083.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_64083.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64104 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64104 with
    | (hd1,args) ->
        let uu____64149 =
          let uu____64164 =
            let uu____64165 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64165.FStar_Syntax_Syntax.n  in
          (uu____64164, args)  in
        (match uu____64149 with
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
         | uu____64237 ->
             (if w
              then
                (let uu____64254 =
                   let uu____64260 =
                     let uu____64262 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____64262
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64260)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64254)
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
    let uu____64299 =
      let uu____64300 = FStar_Syntax_Subst.compress t  in
      uu____64300.FStar_Syntax_Syntax.n  in
    match uu____64299 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____64306;
          FStar_Syntax_Syntax.rng = uu____64307;_}
        ->
        let uu____64310 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64310
    | uu____64311 ->
        (if w
         then
           (let uu____64314 =
              let uu____64320 =
                let uu____64322 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____64322
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64320)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64314)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____64362 uu____64363 =
    let uu____64365 =
      let uu____64371 = FStar_Ident.range_of_id i  in
      let uu____64372 = FStar_Ident.text_of_id i  in
      (uu____64371, uu____64372)  in
    embed repr rng uu____64365  in
  let unembed_ident t w uu____64399 =
    let uu____64404 = unembed' w repr t  in
    match uu____64404 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____64428 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____64428
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____64435 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____64435
  
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
        let uu____64474 =
          let uu____64479 =
            let uu____64480 =
              let uu____64489 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____64489  in
            let uu____64491 =
              let uu____64502 =
                let uu____64511 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____64511  in
              let uu____64512 =
                let uu____64523 =
                  let uu____64532 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____64532  in
                let uu____64535 =
                  let uu____64546 =
                    let uu____64555 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____64555  in
                  let uu____64556 =
                    let uu____64567 =
                      let uu____64576 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____64576  in
                    [uu____64567]  in
                  uu____64546 :: uu____64556  in
                uu____64523 :: uu____64535  in
              uu____64502 :: uu____64512  in
            uu____64480 :: uu____64491  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____64479
           in
        uu____64474 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____64627 =
          let uu____64632 =
            let uu____64633 =
              let uu____64642 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64642  in
            let uu____64646 =
              let uu____64657 =
                let uu____64666 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____64666  in
              [uu____64657]  in
            uu____64633 :: uu____64646  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____64632
           in
        uu____64627 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____64708 =
          let uu____64713 =
            let uu____64714 =
              let uu____64723 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64723  in
            let uu____64727 =
              let uu____64738 =
                let uu____64747 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____64747  in
              let uu____64750 =
                let uu____64761 =
                  let uu____64770 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____64770  in
                let uu____64771 =
                  let uu____64782 =
                    let uu____64791 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____64791  in
                  let uu____64792 =
                    let uu____64803 =
                      let uu____64812 =
                        let uu____64813 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____64813 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____64812  in
                    [uu____64803]  in
                  uu____64782 :: uu____64792  in
                uu____64761 :: uu____64771  in
              uu____64738 :: uu____64750  in
            uu____64714 :: uu____64727  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____64713
           in
        uu____64708 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_64877 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_64877.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_64877.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64896 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64896 with
    | (hd1,args) ->
        let uu____64941 =
          let uu____64954 =
            let uu____64955 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64955.FStar_Syntax_Syntax.n  in
          (uu____64954, args)  in
        (match uu____64941 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____64970)::(us,uu____64972)::(bs,uu____64974)::
            (t2,uu____64976)::(dcs,uu____64978)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____65043 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____65043
               (fun nm1  ->
                  let uu____65061 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____65061
                    (fun us1  ->
                       let uu____65075 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____65075
                         (fun bs1  ->
                            let uu____65081 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____65081
                              (fun t3  ->
                                 let uu____65087 =
                                   let uu____65095 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____65095 dcs  in
                                 FStar_Util.bind_opt uu____65087
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _65125  ->
                                           FStar_Pervasives_Native.Some
                                             _65125)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____65134)::(fvar1,uu____65136)::(univs1,uu____65138)::
            (ty,uu____65140)::(t2,uu____65142)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____65207 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____65207
               (fun r1  ->
                  let uu____65217 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____65217
                    (fun fvar2  ->
                       let uu____65223 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____65223
                         (fun univs2  ->
                            let uu____65237 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____65237
                              (fun ty1  ->
                                 let uu____65243 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____65243
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _65250  ->
                                           FStar_Pervasives_Native.Some
                                             _65250)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____65269 ->
             (if w
              then
                (let uu____65284 =
                   let uu____65290 =
                     let uu____65292 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____65292
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65290)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65284)
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
          let uu____65318 =
            let uu____65323 =
              let uu____65324 =
                let uu____65333 =
                  let uu____65334 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65334  in
                FStar_Syntax_Syntax.as_arg uu____65333  in
              [uu____65324]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____65323
             in
          uu____65318 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____65354 =
            let uu____65359 =
              let uu____65360 =
                let uu____65369 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____65369  in
              let uu____65370 =
                let uu____65381 =
                  let uu____65390 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____65390  in
                [uu____65381]  in
              uu____65360 :: uu____65370  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____65359
             in
          uu____65354 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_65415 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_65415.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_65415.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65436 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65436 with
    | (hd1,args) ->
        let uu____65481 =
          let uu____65494 =
            let uu____65495 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65495.FStar_Syntax_Syntax.n  in
          (uu____65494, args)  in
        (match uu____65481 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65525)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____65550 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65550
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65557  -> FStar_Pervasives_Native.Some _65557)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____65560)::(e2,uu____65562)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____65597 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____65597
               (fun e11  ->
                  let uu____65603 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____65603
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _65610  -> FStar_Pervasives_Native.Some _65610)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____65611 ->
             (if w
              then
                (let uu____65626 =
                   let uu____65632 =
                     let uu____65634 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____65634
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65632)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65626)
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
    let uu____65658 =
      let uu____65663 =
        let uu____65664 =
          let uu____65673 =
            let uu____65674 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____65674  in
          FStar_Syntax_Syntax.as_arg uu____65673  in
        [uu____65664]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____65663
       in
    uu____65658 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65698 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____65698 with
    | (bv,aq) ->
        let uu____65705 =
          let uu____65710 =
            let uu____65711 =
              let uu____65720 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____65720  in
            let uu____65721 =
              let uu____65732 =
                let uu____65741 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____65741  in
              [uu____65732]  in
            uu____65711 :: uu____65721  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____65710
           in
        uu____65705 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65773 =
      let uu____65778 =
        let uu____65779 =
          let uu____65788 =
            let uu____65789 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____65796 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____65789 i.FStar_Syntax_Syntax.rng uu____65796  in
          FStar_Syntax_Syntax.as_arg uu____65788  in
        [uu____65779]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____65778
       in
    uu____65773 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65826 =
      let uu____65831 =
        let uu____65832 =
          let uu____65841 =
            let uu____65842 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____65842  in
          FStar_Syntax_Syntax.as_arg uu____65841  in
        [uu____65832]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____65831
       in
    uu____65826 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65872 =
      let uu____65877 =
        let uu____65878 =
          let uu____65887 =
            let uu____65888 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____65888  in
          FStar_Syntax_Syntax.as_arg uu____65887  in
        [uu____65878]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____65877
       in
    uu____65872 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  