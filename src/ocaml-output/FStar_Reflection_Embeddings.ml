open Prims
let mk_emb :
  'Auu____64264 .
    (FStar_Range.range -> 'Auu____64264 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____64264 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____64264 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____64308 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____64308
  
let embed :
  'Auu____64356 .
    'Auu____64356 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____64356 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____64376 = FStar_Syntax_Embeddings.embed e x  in
        uu____64376 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____64417 .
    Prims.bool ->
      'Auu____64417 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____64417 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____64441 = FStar_Syntax_Embeddings.unembed e x  in
        uu____64441 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____64483 =
      let uu____64484 = FStar_Syntax_Subst.compress t  in
      uu____64484.FStar_Syntax_Syntax.n  in
    match uu____64483 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____64490;
          FStar_Syntax_Syntax.rng = uu____64491;_}
        ->
        let uu____64494 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64494
    | uu____64495 ->
        (if w
         then
           (let uu____64498 =
              let uu____64504 =
                let uu____64506 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____64506  in
              (FStar_Errors.Warning_NotEmbedded, uu____64504)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64498)
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
    let uu____64543 =
      let uu____64544 = FStar_Syntax_Subst.compress t  in
      uu____64544.FStar_Syntax_Syntax.n  in
    match uu____64543 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____64550;
          FStar_Syntax_Syntax.rng = uu____64551;_}
        ->
        let uu____64554 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64554
    | uu____64555 ->
        (if w
         then
           (let uu____64558 =
              let uu____64564 =
                let uu____64566 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____64566
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64564)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64558)
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
          let uu____64618 = f x  in
          FStar_Util.bind_opt uu____64618
            (fun x1  ->
               let uu____64626 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64626
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
        let uu____64695 =
          mapM_opt
            (fun uu____64708  ->
               match uu____64708 with
               | (bv,e) ->
                   let uu____64717 = unembed_term w e  in
                   FStar_Util.bind_opt uu____64717
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____64695
          (fun s  ->
             let uu____64731 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____64731)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____64733 =
        let uu____64734 = FStar_Syntax_Subst.compress t1  in
        uu____64734.FStar_Syntax_Syntax.n  in
      match uu____64733 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____64745 ->
          (if w
           then
             (let uu____64748 =
                let uu____64754 =
                  let uu____64756 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____64756
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____64754)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____64748)
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
          let uu____64791 =
            let uu____64796 =
              let uu____64797 =
                let uu____64806 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____64806  in
              [uu____64797]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____64796
             in
          uu____64791 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_64825 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_64825.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_64825.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64846 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64846 with
    | (hd1,args) ->
        let uu____64891 =
          let uu____64906 =
            let uu____64907 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64907.FStar_Syntax_Syntax.n  in
          (uu____64906, args)  in
        (match uu____64891 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____64962)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____64997 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____64997
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____65002 ->
             (if w
              then
                (let uu____65019 =
                   let uu____65025 =
                     let uu____65027 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____65027
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65025)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65019)
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
    let uu____65067 =
      let uu____65068 = FStar_Syntax_Subst.compress t  in
      uu____65068.FStar_Syntax_Syntax.n  in
    match uu____65067 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____65074;
          FStar_Syntax_Syntax.rng = uu____65075;_}
        ->
        let uu____65078 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65078
    | uu____65079 ->
        (if w
         then
           (let uu____65082 =
              let uu____65088 =
                let uu____65090 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____65090  in
              (FStar_Errors.Warning_NotEmbedded, uu____65088)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65082)
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
    let uu____65127 =
      let uu____65128 = FStar_Syntax_Subst.compress t  in
      uu____65128.FStar_Syntax_Syntax.n  in
    match uu____65127 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____65134;
          FStar_Syntax_Syntax.rng = uu____65135;_}
        ->
        let uu____65138 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65138
    | uu____65139 ->
        (if w
         then
           (let uu____65142 =
              let uu____65148 =
                let uu____65150 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____65150  in
              (FStar_Errors.Warning_NotEmbedded, uu____65148)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65142)
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
    let uu____65187 =
      let uu____65188 = FStar_Syntax_Subst.compress t  in
      uu____65188.FStar_Syntax_Syntax.n  in
    match uu____65187 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____65194;
          FStar_Syntax_Syntax.rng = uu____65195;_}
        ->
        let uu____65198 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65198
    | uu____65199 ->
        (if w
         then
           (let uu____65202 =
              let uu____65208 =
                let uu____65210 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____65210  in
              (FStar_Errors.Warning_NotEmbedded, uu____65208)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65202)
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
          let uu____65236 =
            let uu____65241 =
              let uu____65242 =
                let uu____65251 =
                  let uu____65252 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65252  in
                FStar_Syntax_Syntax.as_arg uu____65251  in
              [uu____65242]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____65241
             in
          uu____65236 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____65274 =
            let uu____65279 =
              let uu____65280 =
                let uu____65289 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____65289  in
              [uu____65280]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____65279
             in
          uu____65274 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____65310 =
            let uu____65315 =
              let uu____65316 =
                let uu____65325 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____65325  in
              [uu____65316]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____65315
             in
          uu____65310 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____65345 =
            let uu____65350 =
              let uu____65351 =
                let uu____65360 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____65360  in
              [uu____65351]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____65350
             in
          uu____65345 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_65382 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_65382.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_65382.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65403 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65403 with
    | (hd1,args) ->
        let uu____65448 =
          let uu____65463 =
            let uu____65464 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65464.FStar_Syntax_Syntax.n  in
          (uu____65463, args)  in
        (match uu____65448 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65538)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____65573 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65573
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65580  -> FStar_Pervasives_Native.Some _65580)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____65583)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____65618 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____65618
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _65629  -> FStar_Pervasives_Native.Some _65629)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____65632)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____65667 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____65667
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _65674  -> FStar_Pervasives_Native.Some _65674)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _65696  -> FStar_Pervasives_Native.Some _65696)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____65699)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____65734 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____65734
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _65753  -> FStar_Pervasives_Native.Some _65753)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____65754 ->
             (if w
              then
                (let uu____65771 =
                   let uu____65777 =
                     let uu____65779 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____65779
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65777)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65771)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____65792  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65805 =
            let uu____65810 =
              let uu____65811 =
                let uu____65820 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____65820  in
              [uu____65811]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____65810
             in
          uu____65805 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65845 =
            let uu____65850 =
              let uu____65851 =
                let uu____65860 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____65860  in
              let uu____65861 =
                let uu____65872 =
                  let uu____65881 =
                    let uu____65882 =
                      let uu____65887 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____65887  in
                    embed uu____65882 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____65881  in
                [uu____65872]  in
              uu____65851 :: uu____65861  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____65850
             in
          uu____65845 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65919 =
            let uu____65924 =
              let uu____65925 =
                let uu____65934 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65934  in
              [uu____65925]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____65924
             in
          uu____65919 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65954 =
            let uu____65959 =
              let uu____65960 =
                let uu____65969 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65969  in
              [uu____65960]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____65959
             in
          uu____65954 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65990 =
            let uu____65995 =
              let uu____65996 =
                let uu____66005 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66005  in
              let uu____66006 =
                let uu____66017 =
                  let uu____66026 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____66026  in
                [uu____66017]  in
              uu____65996 :: uu____66006  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____65995
             in
          uu____65990 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____66071 = FStar_Syntax_Util.head_and_args t1  in
      match uu____66071 with
      | (hd1,args) ->
          let uu____66116 =
            let uu____66129 =
              let uu____66130 = FStar_Syntax_Util.un_uinst hd1  in
              uu____66130.FStar_Syntax_Syntax.n  in
            (uu____66129, args)  in
          (match uu____66116 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____66145)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____66170 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____66170
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _66177  -> FStar_Pervasives_Native.Some _66177)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____66180)::(ps,uu____66182)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____66217 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____66217
                 (fun f1  ->
                    let uu____66223 =
                      let uu____66228 =
                        let uu____66233 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____66233  in
                      unembed' w uu____66228 ps  in
                    FStar_Util.bind_opt uu____66223
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _66246  ->
                              FStar_Pervasives_Native.Some _66246)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66251)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____66276 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66276
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66283  -> FStar_Pervasives_Native.Some _66283)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66286)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____66311 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66311
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66318  -> FStar_Pervasives_Native.Some _66318)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____66321)::(t2,uu____66323)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____66358 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66358
                 (fun bv1  ->
                    let uu____66364 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____66364
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _66371  ->
                              FStar_Pervasives_Native.Some _66371)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____66372 ->
               (if w
                then
                  (let uu____66387 =
                     let uu____66393 =
                       let uu____66395 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____66395
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____66393)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____66387)
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
    let uu____66422 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____66422
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____66437 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____66437 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____66460 =
            let uu____66465 =
              let uu____66466 =
                let uu____66475 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66475  in
              [uu____66466]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____66465
             in
          uu____66460 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____66495 =
            let uu____66500 =
              let uu____66501 =
                let uu____66510 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66510  in
              [uu____66501]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____66500
             in
          uu____66495 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____66530 =
            let uu____66535 =
              let uu____66536 =
                let uu____66545 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66545  in
              [uu____66536]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____66535
             in
          uu____66530 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66566 =
            let uu____66571 =
              let uu____66572 =
                let uu____66581 =
                  let uu____66582 = e_term_aq aq  in
                  embed uu____66582 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____66581  in
              let uu____66585 =
                let uu____66596 =
                  let uu____66605 =
                    let uu____66606 = e_argv_aq aq  in
                    embed uu____66606 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____66605  in
                [uu____66596]  in
              uu____66572 :: uu____66585  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____66571
             in
          uu____66566 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____66645 =
            let uu____66650 =
              let uu____66651 =
                let uu____66660 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66660  in
              let uu____66661 =
                let uu____66672 =
                  let uu____66681 =
                    let uu____66682 = e_term_aq aq  in
                    embed uu____66682 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66681  in
                [uu____66672]  in
              uu____66651 :: uu____66661  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____66650
             in
          uu____66645 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66713 =
            let uu____66718 =
              let uu____66719 =
                let uu____66728 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66728  in
              let uu____66729 =
                let uu____66740 =
                  let uu____66749 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____66749  in
                [uu____66740]  in
              uu____66719 :: uu____66729  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____66718
             in
          uu____66713 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66777 =
            let uu____66782 =
              let uu____66783 =
                let uu____66792 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____66792  in
              [uu____66783]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____66782
             in
          uu____66777 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____66813 =
            let uu____66818 =
              let uu____66819 =
                let uu____66828 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66828  in
              let uu____66829 =
                let uu____66840 =
                  let uu____66849 =
                    let uu____66850 = e_term_aq aq  in
                    embed uu____66850 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66849  in
                [uu____66840]  in
              uu____66819 :: uu____66829  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____66818
             in
          uu____66813 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66880 =
            let uu____66885 =
              let uu____66886 =
                let uu____66895 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____66895  in
              [uu____66886]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____66885
             in
          uu____66880 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66916 =
            let uu____66921 =
              let uu____66922 =
                let uu____66931 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____66931  in
              let uu____66932 =
                let uu____66943 =
                  let uu____66952 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____66952  in
                [uu____66943]  in
              uu____66922 :: uu____66932  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____66921
             in
          uu____66916 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66989 =
            let uu____66994 =
              let uu____66995 =
                let uu____67004 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____67004  in
              let uu____67006 =
                let uu____67017 =
                  let uu____67026 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____67026  in
                let uu____67027 =
                  let uu____67038 =
                    let uu____67047 =
                      let uu____67048 = e_term_aq aq  in
                      embed uu____67048 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____67047  in
                  let uu____67051 =
                    let uu____67062 =
                      let uu____67071 =
                        let uu____67072 = e_term_aq aq  in
                        embed uu____67072 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____67071  in
                    [uu____67062]  in
                  uu____67038 :: uu____67051  in
                uu____67017 :: uu____67027  in
              uu____66995 :: uu____67006  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____66994
             in
          uu____66989 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____67123 =
            let uu____67128 =
              let uu____67129 =
                let uu____67138 =
                  let uu____67139 = e_term_aq aq  in embed uu____67139 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____67138  in
              let uu____67142 =
                let uu____67153 =
                  let uu____67162 =
                    let uu____67163 =
                      let uu____67172 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____67172  in
                    embed uu____67163 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____67162  in
                [uu____67153]  in
              uu____67129 :: uu____67142  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____67128
             in
          uu____67123 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____67222 =
            let uu____67227 =
              let uu____67228 =
                let uu____67237 =
                  let uu____67238 = e_term_aq aq  in embed uu____67238 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67237  in
              let uu____67241 =
                let uu____67252 =
                  let uu____67261 =
                    let uu____67262 = e_term_aq aq  in
                    embed uu____67262 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____67261  in
                let uu____67265 =
                  let uu____67276 =
                    let uu____67285 =
                      let uu____67286 =
                        let uu____67291 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67291  in
                      embed uu____67286 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67285  in
                  [uu____67276]  in
                uu____67252 :: uu____67265  in
              uu____67228 :: uu____67241  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____67227
             in
          uu____67222 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____67337 =
            let uu____67342 =
              let uu____67343 =
                let uu____67352 =
                  let uu____67353 = e_term_aq aq  in embed uu____67353 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67352  in
              let uu____67356 =
                let uu____67367 =
                  let uu____67376 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____67376  in
                let uu____67377 =
                  let uu____67388 =
                    let uu____67397 =
                      let uu____67398 =
                        let uu____67403 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67403  in
                      embed uu____67398 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67397  in
                  [uu____67388]  in
                uu____67367 :: uu____67377  in
              uu____67343 :: uu____67356  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____67342
             in
          uu____67337 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_67442 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_67442.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_67442.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____67460 = FStar_Syntax_Util.head_and_args t  in
      match uu____67460 with
      | (hd1,args) ->
          let uu____67505 =
            let uu____67518 =
              let uu____67519 = FStar_Syntax_Util.un_uinst hd1  in
              uu____67519.FStar_Syntax_Syntax.n  in
            (uu____67518, args)  in
          (match uu____67505 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67534)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____67559 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67559
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67566  -> FStar_Pervasives_Native.Some _67566)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67569)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____67594 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67594
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67601  -> FStar_Pervasives_Native.Some _67601)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____67604)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____67629 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____67629
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _67636  -> FStar_Pervasives_Native.Some _67636)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____67639)::(r,uu____67641)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____67676 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____67676
                 (fun l1  ->
                    let uu____67682 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____67682
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _67689  ->
                              FStar_Pervasives_Native.Some _67689)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67692)::(t1,uu____67694)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____67729 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67729
                 (fun b1  ->
                    let uu____67735 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67735
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67742  ->
                              FStar_Pervasives_Native.Some _67742)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67745)::(t1,uu____67747)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____67782 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67782
                 (fun b1  ->
                    let uu____67788 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____67788
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _67795  ->
                              FStar_Pervasives_Native.Some _67795)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____67798)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____67823 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____67823
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _67830  -> FStar_Pervasives_Native.Some _67830)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67833)::(t1,uu____67835)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____67870 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67870
                 (fun b1  ->
                    let uu____67876 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67876
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67883  ->
                              FStar_Pervasives_Native.Some _67883)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____67886)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____67911 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____67911
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _67918  -> FStar_Pervasives_Native.Some _67918)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____67921)::(l,uu____67923)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____67958 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____67958
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _67967  -> FStar_Pervasives_Native.Some _67967)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____67970)::(b,uu____67972)::(t1,uu____67974)::
              (t2,uu____67976)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____68031 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____68031
                 (fun r1  ->
                    let uu____68041 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____68041
                      (fun b1  ->
                         let uu____68047 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____68047
                           (fun t11  ->
                              let uu____68053 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____68053
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _68060  ->
                                        FStar_Pervasives_Native.Some _68060)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____68064)::(brs,uu____68066)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____68101 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____68101
                 (fun t2  ->
                    let uu____68107 =
                      let uu____68112 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____68112 brs  in
                    FStar_Util.bind_opt uu____68107
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _68127  ->
                              FStar_Pervasives_Native.Some _68127)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68132)::(t1,uu____68134)::(tacopt,uu____68136)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____68181 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68181
                 (fun e1  ->
                    let uu____68187 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____68187
                      (fun t2  ->
                         let uu____68193 =
                           let uu____68198 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68198 tacopt  in
                         FStar_Util.bind_opt uu____68193
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68213  ->
                                   FStar_Pervasives_Native.Some _68213)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68218)::(c,uu____68220)::(tacopt,uu____68222)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____68267 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68267
                 (fun e1  ->
                    let uu____68273 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____68273
                      (fun c1  ->
                         let uu____68279 =
                           let uu____68284 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68284 tacopt  in
                         FStar_Util.bind_opt uu____68279
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68299  ->
                                   FStar_Pervasives_Native.Some _68299)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _68319  -> FStar_Pervasives_Native.Some _68319)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____68320 ->
               (if w
                then
                  (let uu____68335 =
                     let uu____68341 =
                       let uu____68343 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____68343
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____68341)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____68335)
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
    let uu____68372 =
      let uu____68377 =
        let uu____68378 =
          let uu____68387 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____68387  in
        let uu____68389 =
          let uu____68400 =
            let uu____68409 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____68409  in
          let uu____68410 =
            let uu____68421 =
              let uu____68430 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____68430  in
            [uu____68421]  in
          uu____68400 :: uu____68410  in
        uu____68378 :: uu____68389  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____68377
       in
    uu____68372 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68483 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68483 with
    | (hd1,args) ->
        let uu____68528 =
          let uu____68541 =
            let uu____68542 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68542.FStar_Syntax_Syntax.n  in
          (uu____68541, args)  in
        (match uu____68528 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____68557)::(idx,uu____68559)::(s,uu____68561)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____68606 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____68606
               (fun nm1  ->
                  let uu____68616 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____68616
                    (fun idx1  ->
                       let uu____68622 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____68622
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _68629  ->
                                 FStar_Pervasives_Native.Some _68629)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____68630 ->
             (if w
              then
                (let uu____68645 =
                   let uu____68651 =
                     let uu____68653 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____68653
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____68651)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____68645)
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
        let uu____68679 =
          let uu____68684 =
            let uu____68685 =
              let uu____68694 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____68694  in
            let uu____68695 =
              let uu____68706 =
                let uu____68715 =
                  let uu____68716 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____68716 rng md  in
                FStar_Syntax_Syntax.as_arg uu____68715  in
              [uu____68706]  in
            uu____68685 :: uu____68695  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____68684
           in
        uu____68679 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____68754 =
          let uu____68759 =
            let uu____68760 =
              let uu____68769 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____68769  in
            let uu____68770 =
              let uu____68781 =
                let uu____68790 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____68790  in
              [uu____68781]  in
            uu____68760 :: uu____68770  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____68759
           in
        uu____68754 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_68817 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_68817.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_68817.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68836 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68836 with
    | (hd1,args) ->
        let uu____68881 =
          let uu____68894 =
            let uu____68895 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68895.FStar_Syntax_Syntax.n  in
          (uu____68894, args)  in
        (match uu____68881 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____68910)::(md,uu____68912)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____68947 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____68947
               (fun t3  ->
                  let uu____68953 =
                    let uu____68958 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____68958 md  in
                  FStar_Util.bind_opt uu____68953
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _68973  -> FStar_Pervasives_Native.Some _68973)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____68978)::(post,uu____68980)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____69015 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____69015
               (fun pre1  ->
                  let uu____69021 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____69021
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _69028  -> FStar_Pervasives_Native.Some _69028)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _69046  -> FStar_Pervasives_Native.Some _69046)
               FStar_Reflection_Data.C_Unknown
         | uu____69047 ->
             (if w
              then
                (let uu____69062 =
                   let uu____69068 =
                     let uu____69070 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____69070
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69068)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69062)
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
    let uu___1175_69095 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_69095.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_69095.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69116 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69116 with
    | (hd1,args) ->
        let uu____69161 =
          let uu____69176 =
            let uu____69177 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69177.FStar_Syntax_Syntax.n  in
          (uu____69176, args)  in
        (match uu____69161 with
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
         | uu____69249 ->
             (if w
              then
                (let uu____69266 =
                   let uu____69272 =
                     let uu____69274 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____69274
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69272)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69266)
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
    let uu____69311 =
      let uu____69312 = FStar_Syntax_Subst.compress t  in
      uu____69312.FStar_Syntax_Syntax.n  in
    match uu____69311 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____69318;
          FStar_Syntax_Syntax.rng = uu____69319;_}
        ->
        let uu____69322 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____69322
    | uu____69323 ->
        (if w
         then
           (let uu____69326 =
              let uu____69332 =
                let uu____69334 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____69334
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____69332)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69326)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____69394 uu____69395 =
    let uu____69417 =
      let uu____69423 = FStar_Ident.range_of_id i  in
      let uu____69424 = FStar_Ident.text_of_id i  in
      (uu____69423, uu____69424)  in
    embed repr rng uu____69417  in
  let unembed_ident t w uu____69452 =
    let uu____69458 = unembed' w repr t  in
    match uu____69458 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____69482 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____69482
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____69489 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____69489
  
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
        let uu____69528 =
          let uu____69533 =
            let uu____69534 =
              let uu____69543 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____69543  in
            let uu____69545 =
              let uu____69556 =
                let uu____69565 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____69565  in
              let uu____69566 =
                let uu____69577 =
                  let uu____69586 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____69586  in
                let uu____69589 =
                  let uu____69600 =
                    let uu____69609 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____69609  in
                  let uu____69610 =
                    let uu____69621 =
                      let uu____69630 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____69630  in
                    [uu____69621]  in
                  uu____69600 :: uu____69610  in
                uu____69577 :: uu____69589  in
              uu____69556 :: uu____69566  in
            uu____69534 :: uu____69545  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____69533
           in
        uu____69528 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____69683 =
          let uu____69688 =
            let uu____69689 =
              let uu____69698 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69698  in
            let uu____69702 =
              let uu____69713 =
                let uu____69722 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____69722  in
              [uu____69713]  in
            uu____69689 :: uu____69702  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____69688
           in
        uu____69683 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____69766 =
          let uu____69771 =
            let uu____69772 =
              let uu____69781 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69781  in
            let uu____69785 =
              let uu____69796 =
                let uu____69805 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____69805  in
              let uu____69808 =
                let uu____69819 =
                  let uu____69828 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____69828  in
                let uu____69829 =
                  let uu____69840 =
                    let uu____69849 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____69849  in
                  let uu____69850 =
                    let uu____69861 =
                      let uu____69870 =
                        let uu____69871 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____69871 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____69870  in
                    [uu____69861]  in
                  uu____69840 :: uu____69850  in
                uu____69819 :: uu____69829  in
              uu____69796 :: uu____69808  in
            uu____69772 :: uu____69785  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____69771
           in
        uu____69766 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_69937 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_69937.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_69937.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69956 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69956 with
    | (hd1,args) ->
        let uu____70001 =
          let uu____70014 =
            let uu____70015 = FStar_Syntax_Util.un_uinst hd1  in
            uu____70015.FStar_Syntax_Syntax.n  in
          (uu____70014, args)  in
        (match uu____70001 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____70030)::(us,uu____70032)::(bs,uu____70034)::
            (t2,uu____70036)::(dcs,uu____70038)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____70103 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____70103
               (fun nm1  ->
                  let uu____70121 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____70121
                    (fun us1  ->
                       let uu____70135 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____70135
                         (fun bs1  ->
                            let uu____70141 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____70141
                              (fun t3  ->
                                 let uu____70147 =
                                   let uu____70155 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____70155 dcs  in
                                 FStar_Util.bind_opt uu____70147
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _70185  ->
                                           FStar_Pervasives_Native.Some
                                             _70185)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____70194)::(fvar1,uu____70196)::(univs1,uu____70198)::
            (ty,uu____70200)::(t2,uu____70202)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____70267 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____70267
               (fun r1  ->
                  let uu____70277 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____70277
                    (fun fvar2  ->
                       let uu____70283 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____70283
                         (fun univs2  ->
                            let uu____70297 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____70297
                              (fun ty1  ->
                                 let uu____70303 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____70303
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _70310  ->
                                           FStar_Pervasives_Native.Some
                                             _70310)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____70329 ->
             (if w
              then
                (let uu____70344 =
                   let uu____70350 =
                     let uu____70352 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____70352
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70350)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70344)
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
          let uu____70378 =
            let uu____70383 =
              let uu____70384 =
                let uu____70393 =
                  let uu____70394 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____70394  in
                FStar_Syntax_Syntax.as_arg uu____70393  in
              [uu____70384]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____70383
             in
          uu____70378 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____70416 =
            let uu____70421 =
              let uu____70422 =
                let uu____70431 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____70431  in
              let uu____70432 =
                let uu____70443 =
                  let uu____70452 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____70452  in
                [uu____70443]  in
              uu____70422 :: uu____70432  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____70421
             in
          uu____70416 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_70479 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_70479.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_70479.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____70500 = FStar_Syntax_Util.head_and_args t1  in
    match uu____70500 with
    | (hd1,args) ->
        let uu____70545 =
          let uu____70558 =
            let uu____70559 = FStar_Syntax_Util.un_uinst hd1  in
            uu____70559.FStar_Syntax_Syntax.n  in
          (uu____70558, args)  in
        (match uu____70545 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____70589)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____70614 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____70614
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _70621  -> FStar_Pervasives_Native.Some _70621)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____70624)::(e2,uu____70626)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____70661 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____70661
               (fun e11  ->
                  let uu____70667 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____70667
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _70674  -> FStar_Pervasives_Native.Some _70674)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____70675 ->
             (if w
              then
                (let uu____70690 =
                   let uu____70696 =
                     let uu____70698 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____70698
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70696)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70690)
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
    let uu____70722 =
      let uu____70727 =
        let uu____70728 =
          let uu____70737 =
            let uu____70738 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____70738  in
          FStar_Syntax_Syntax.as_arg uu____70737  in
        [uu____70728]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____70727
       in
    uu____70722 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70764 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____70764 with
    | (bv,aq) ->
        let uu____70771 =
          let uu____70776 =
            let uu____70777 =
              let uu____70786 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____70786  in
            let uu____70787 =
              let uu____70798 =
                let uu____70807 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____70807  in
              [uu____70798]  in
            uu____70777 :: uu____70787  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____70776
           in
        uu____70771 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70841 =
      let uu____70846 =
        let uu____70847 =
          let uu____70856 =
            let uu____70857 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____70864 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____70857 i.FStar_Syntax_Syntax.rng uu____70864  in
          FStar_Syntax_Syntax.as_arg uu____70856  in
        [uu____70847]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____70846
       in
    uu____70841 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70896 =
      let uu____70901 =
        let uu____70902 =
          let uu____70911 =
            let uu____70912 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____70912  in
          FStar_Syntax_Syntax.as_arg uu____70911  in
        [uu____70902]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____70901
       in
    uu____70896 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70944 =
      let uu____70949 =
        let uu____70950 =
          let uu____70959 =
            let uu____70960 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____70960  in
          FStar_Syntax_Syntax.as_arg uu____70959  in
        [uu____70950]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____70949
       in
    uu____70944 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  