open Prims
let mk_emb :
  'Auu____64236 .
    (FStar_Range.range -> 'Auu____64236 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____64236 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____64236 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____64280 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____64280
  
let embed :
  'Auu____64328 .
    'Auu____64328 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____64328 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____64348 = FStar_Syntax_Embeddings.embed e x  in
        uu____64348 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____64389 .
    Prims.bool ->
      'Auu____64389 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____64389 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____64413 = FStar_Syntax_Embeddings.unembed e x  in
        uu____64413 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____64455 =
      let uu____64456 = FStar_Syntax_Subst.compress t  in
      uu____64456.FStar_Syntax_Syntax.n  in
    match uu____64455 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____64462;
          FStar_Syntax_Syntax.rng = uu____64463;_}
        ->
        let uu____64466 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64466
    | uu____64467 ->
        (if w
         then
           (let uu____64470 =
              let uu____64476 =
                let uu____64478 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____64478  in
              (FStar_Errors.Warning_NotEmbedded, uu____64476)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64470)
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
    let uu____64515 =
      let uu____64516 = FStar_Syntax_Subst.compress t  in
      uu____64516.FStar_Syntax_Syntax.n  in
    match uu____64515 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____64522;
          FStar_Syntax_Syntax.rng = uu____64523;_}
        ->
        let uu____64526 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64526
    | uu____64527 ->
        (if w
         then
           (let uu____64530 =
              let uu____64536 =
                let uu____64538 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____64538
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64536)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64530)
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
          let uu____64590 = f x  in
          FStar_Util.bind_opt uu____64590
            (fun x1  ->
               let uu____64598 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64598
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
        let uu____64667 =
          mapM_opt
            (fun uu____64680  ->
               match uu____64680 with
               | (bv,e) ->
                   let uu____64689 = unembed_term w e  in
                   FStar_Util.bind_opt uu____64689
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____64667
          (fun s  ->
             let uu____64703 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____64703)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____64705 =
        let uu____64706 = FStar_Syntax_Subst.compress t1  in
        uu____64706.FStar_Syntax_Syntax.n  in
      match uu____64705 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____64717 ->
          (if w
           then
             (let uu____64720 =
                let uu____64726 =
                  let uu____64728 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____64728
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____64726)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____64720)
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
          let uu____64763 =
            let uu____64768 =
              let uu____64769 =
                let uu____64778 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____64778  in
              [uu____64769]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____64768
             in
          uu____64763 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_64797 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_64797.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_64797.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64818 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64818 with
    | (hd1,args) ->
        let uu____64863 =
          let uu____64878 =
            let uu____64879 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64879.FStar_Syntax_Syntax.n  in
          (uu____64878, args)  in
        (match uu____64863 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____64934)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____64969 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____64969
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____64974 ->
             (if w
              then
                (let uu____64991 =
                   let uu____64997 =
                     let uu____64999 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____64999
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64997)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64991)
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
    let uu____65039 =
      let uu____65040 = FStar_Syntax_Subst.compress t  in
      uu____65040.FStar_Syntax_Syntax.n  in
    match uu____65039 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____65046;
          FStar_Syntax_Syntax.rng = uu____65047;_}
        ->
        let uu____65050 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65050
    | uu____65051 ->
        (if w
         then
           (let uu____65054 =
              let uu____65060 =
                let uu____65062 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____65062  in
              (FStar_Errors.Warning_NotEmbedded, uu____65060)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65054)
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
    let uu____65099 =
      let uu____65100 = FStar_Syntax_Subst.compress t  in
      uu____65100.FStar_Syntax_Syntax.n  in
    match uu____65099 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____65106;
          FStar_Syntax_Syntax.rng = uu____65107;_}
        ->
        let uu____65110 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65110
    | uu____65111 ->
        (if w
         then
           (let uu____65114 =
              let uu____65120 =
                let uu____65122 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____65122  in
              (FStar_Errors.Warning_NotEmbedded, uu____65120)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65114)
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
    let uu____65159 =
      let uu____65160 = FStar_Syntax_Subst.compress t  in
      uu____65160.FStar_Syntax_Syntax.n  in
    match uu____65159 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____65166;
          FStar_Syntax_Syntax.rng = uu____65167;_}
        ->
        let uu____65170 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65170
    | uu____65171 ->
        (if w
         then
           (let uu____65174 =
              let uu____65180 =
                let uu____65182 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____65182  in
              (FStar_Errors.Warning_NotEmbedded, uu____65180)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65174)
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
          let uu____65208 =
            let uu____65213 =
              let uu____65214 =
                let uu____65223 =
                  let uu____65224 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65224  in
                FStar_Syntax_Syntax.as_arg uu____65223  in
              [uu____65214]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____65213
             in
          uu____65208 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____65246 =
            let uu____65251 =
              let uu____65252 =
                let uu____65261 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____65261  in
              [uu____65252]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____65251
             in
          uu____65246 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____65282 =
            let uu____65287 =
              let uu____65288 =
                let uu____65297 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____65297  in
              [uu____65288]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____65287
             in
          uu____65282 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____65317 =
            let uu____65322 =
              let uu____65323 =
                let uu____65332 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____65332  in
              [uu____65323]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____65322
             in
          uu____65317 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_65354 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_65354.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_65354.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65375 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65375 with
    | (hd1,args) ->
        let uu____65420 =
          let uu____65435 =
            let uu____65436 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65436.FStar_Syntax_Syntax.n  in
          (uu____65435, args)  in
        (match uu____65420 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65510)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____65545 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65545
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65552  -> FStar_Pervasives_Native.Some _65552)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____65555)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____65590 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____65590
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _65601  -> FStar_Pervasives_Native.Some _65601)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____65604)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____65639 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____65639
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _65646  -> FStar_Pervasives_Native.Some _65646)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _65668  -> FStar_Pervasives_Native.Some _65668)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____65671)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____65706 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____65706
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _65725  -> FStar_Pervasives_Native.Some _65725)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____65726 ->
             (if w
              then
                (let uu____65743 =
                   let uu____65749 =
                     let uu____65751 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____65751
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65749)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65743)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____65764  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65777 =
            let uu____65782 =
              let uu____65783 =
                let uu____65792 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____65792  in
              [uu____65783]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____65782
             in
          uu____65777 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65817 =
            let uu____65822 =
              let uu____65823 =
                let uu____65832 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____65832  in
              let uu____65833 =
                let uu____65844 =
                  let uu____65853 =
                    let uu____65854 =
                      let uu____65859 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____65859  in
                    embed uu____65854 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____65853  in
                [uu____65844]  in
              uu____65823 :: uu____65833  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____65822
             in
          uu____65817 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65891 =
            let uu____65896 =
              let uu____65897 =
                let uu____65906 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65906  in
              [uu____65897]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____65896
             in
          uu____65891 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65926 =
            let uu____65931 =
              let uu____65932 =
                let uu____65941 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65941  in
              [uu____65932]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____65931
             in
          uu____65926 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65962 =
            let uu____65967 =
              let uu____65968 =
                let uu____65977 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65977  in
              let uu____65978 =
                let uu____65989 =
                  let uu____65998 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____65998  in
                [uu____65989]  in
              uu____65968 :: uu____65978  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____65967
             in
          uu____65962 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____66043 = FStar_Syntax_Util.head_and_args t1  in
      match uu____66043 with
      | (hd1,args) ->
          let uu____66088 =
            let uu____66101 =
              let uu____66102 = FStar_Syntax_Util.un_uinst hd1  in
              uu____66102.FStar_Syntax_Syntax.n  in
            (uu____66101, args)  in
          (match uu____66088 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____66117)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____66142 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____66142
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _66149  -> FStar_Pervasives_Native.Some _66149)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____66152)::(ps,uu____66154)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____66189 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____66189
                 (fun f1  ->
                    let uu____66195 =
                      let uu____66200 =
                        let uu____66205 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____66205  in
                      unembed' w uu____66200 ps  in
                    FStar_Util.bind_opt uu____66195
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _66218  ->
                              FStar_Pervasives_Native.Some _66218)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66223)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____66248 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66248
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66255  -> FStar_Pervasives_Native.Some _66255)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66258)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____66283 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66283
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66290  -> FStar_Pervasives_Native.Some _66290)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____66293)::(t2,uu____66295)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____66330 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66330
                 (fun bv1  ->
                    let uu____66336 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____66336
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _66343  ->
                              FStar_Pervasives_Native.Some _66343)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____66344 ->
               (if w
                then
                  (let uu____66359 =
                     let uu____66365 =
                       let uu____66367 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____66367
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____66365)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____66359)
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
    let uu____66394 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____66394
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____66409 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____66409 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____66432 =
            let uu____66437 =
              let uu____66438 =
                let uu____66447 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66447  in
              [uu____66438]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____66437
             in
          uu____66432 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____66467 =
            let uu____66472 =
              let uu____66473 =
                let uu____66482 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66482  in
              [uu____66473]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____66472
             in
          uu____66467 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____66502 =
            let uu____66507 =
              let uu____66508 =
                let uu____66517 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66517  in
              [uu____66508]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____66507
             in
          uu____66502 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66538 =
            let uu____66543 =
              let uu____66544 =
                let uu____66553 =
                  let uu____66554 = e_term_aq aq  in
                  embed uu____66554 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____66553  in
              let uu____66557 =
                let uu____66568 =
                  let uu____66577 =
                    let uu____66578 = e_argv_aq aq  in
                    embed uu____66578 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____66577  in
                [uu____66568]  in
              uu____66544 :: uu____66557  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____66543
             in
          uu____66538 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____66617 =
            let uu____66622 =
              let uu____66623 =
                let uu____66632 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66632  in
              let uu____66633 =
                let uu____66644 =
                  let uu____66653 =
                    let uu____66654 = e_term_aq aq  in
                    embed uu____66654 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66653  in
                [uu____66644]  in
              uu____66623 :: uu____66633  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____66622
             in
          uu____66617 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66685 =
            let uu____66690 =
              let uu____66691 =
                let uu____66700 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66700  in
              let uu____66701 =
                let uu____66712 =
                  let uu____66721 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____66721  in
                [uu____66712]  in
              uu____66691 :: uu____66701  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____66690
             in
          uu____66685 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66749 =
            let uu____66754 =
              let uu____66755 =
                let uu____66764 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____66764  in
              [uu____66755]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____66754
             in
          uu____66749 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____66785 =
            let uu____66790 =
              let uu____66791 =
                let uu____66800 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66800  in
              let uu____66801 =
                let uu____66812 =
                  let uu____66821 =
                    let uu____66822 = e_term_aq aq  in
                    embed uu____66822 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66821  in
                [uu____66812]  in
              uu____66791 :: uu____66801  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____66790
             in
          uu____66785 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66852 =
            let uu____66857 =
              let uu____66858 =
                let uu____66867 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____66867  in
              [uu____66858]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____66857
             in
          uu____66852 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66888 =
            let uu____66893 =
              let uu____66894 =
                let uu____66903 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____66903  in
              let uu____66904 =
                let uu____66915 =
                  let uu____66924 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____66924  in
                [uu____66915]  in
              uu____66894 :: uu____66904  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____66893
             in
          uu____66888 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66961 =
            let uu____66966 =
              let uu____66967 =
                let uu____66976 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____66976  in
              let uu____66978 =
                let uu____66989 =
                  let uu____66998 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____66998  in
                let uu____66999 =
                  let uu____67010 =
                    let uu____67019 =
                      let uu____67020 = e_term_aq aq  in
                      embed uu____67020 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____67019  in
                  let uu____67023 =
                    let uu____67034 =
                      let uu____67043 =
                        let uu____67044 = e_term_aq aq  in
                        embed uu____67044 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____67043  in
                    [uu____67034]  in
                  uu____67010 :: uu____67023  in
                uu____66989 :: uu____66999  in
              uu____66967 :: uu____66978  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____66966
             in
          uu____66961 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____67095 =
            let uu____67100 =
              let uu____67101 =
                let uu____67110 =
                  let uu____67111 = e_term_aq aq  in embed uu____67111 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____67110  in
              let uu____67114 =
                let uu____67125 =
                  let uu____67134 =
                    let uu____67135 =
                      let uu____67144 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____67144  in
                    embed uu____67135 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____67134  in
                [uu____67125]  in
              uu____67101 :: uu____67114  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____67100
             in
          uu____67095 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____67194 =
            let uu____67199 =
              let uu____67200 =
                let uu____67209 =
                  let uu____67210 = e_term_aq aq  in embed uu____67210 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67209  in
              let uu____67213 =
                let uu____67224 =
                  let uu____67233 =
                    let uu____67234 = e_term_aq aq  in
                    embed uu____67234 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____67233  in
                let uu____67237 =
                  let uu____67248 =
                    let uu____67257 =
                      let uu____67258 =
                        let uu____67263 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67263  in
                      embed uu____67258 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67257  in
                  [uu____67248]  in
                uu____67224 :: uu____67237  in
              uu____67200 :: uu____67213  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____67199
             in
          uu____67194 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____67309 =
            let uu____67314 =
              let uu____67315 =
                let uu____67324 =
                  let uu____67325 = e_term_aq aq  in embed uu____67325 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67324  in
              let uu____67328 =
                let uu____67339 =
                  let uu____67348 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____67348  in
                let uu____67349 =
                  let uu____67360 =
                    let uu____67369 =
                      let uu____67370 =
                        let uu____67375 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67375  in
                      embed uu____67370 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67369  in
                  [uu____67360]  in
                uu____67339 :: uu____67349  in
              uu____67315 :: uu____67328  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____67314
             in
          uu____67309 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_67414 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_67414.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_67414.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____67432 = FStar_Syntax_Util.head_and_args t  in
      match uu____67432 with
      | (hd1,args) ->
          let uu____67477 =
            let uu____67490 =
              let uu____67491 = FStar_Syntax_Util.un_uinst hd1  in
              uu____67491.FStar_Syntax_Syntax.n  in
            (uu____67490, args)  in
          (match uu____67477 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67506)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____67531 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67531
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67538  -> FStar_Pervasives_Native.Some _67538)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67541)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____67566 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67566
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67573  -> FStar_Pervasives_Native.Some _67573)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____67576)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____67601 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____67601
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _67608  -> FStar_Pervasives_Native.Some _67608)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____67611)::(r,uu____67613)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____67648 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____67648
                 (fun l1  ->
                    let uu____67654 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____67654
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _67661  ->
                              FStar_Pervasives_Native.Some _67661)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67664)::(t1,uu____67666)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____67701 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67701
                 (fun b1  ->
                    let uu____67707 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67707
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67714  ->
                              FStar_Pervasives_Native.Some _67714)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67717)::(t1,uu____67719)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____67754 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67754
                 (fun b1  ->
                    let uu____67760 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____67760
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _67767  ->
                              FStar_Pervasives_Native.Some _67767)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____67770)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____67795 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____67795
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _67802  -> FStar_Pervasives_Native.Some _67802)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67805)::(t1,uu____67807)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____67842 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67842
                 (fun b1  ->
                    let uu____67848 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67848
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67855  ->
                              FStar_Pervasives_Native.Some _67855)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____67858)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____67883 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____67883
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _67890  -> FStar_Pervasives_Native.Some _67890)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____67893)::(l,uu____67895)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____67930 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____67930
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _67939  -> FStar_Pervasives_Native.Some _67939)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____67942)::(b,uu____67944)::(t1,uu____67946)::
              (t2,uu____67948)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____68003 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____68003
                 (fun r1  ->
                    let uu____68013 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____68013
                      (fun b1  ->
                         let uu____68019 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____68019
                           (fun t11  ->
                              let uu____68025 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____68025
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _68032  ->
                                        FStar_Pervasives_Native.Some _68032)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____68036)::(brs,uu____68038)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____68073 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____68073
                 (fun t2  ->
                    let uu____68079 =
                      let uu____68084 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____68084 brs  in
                    FStar_Util.bind_opt uu____68079
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _68099  ->
                              FStar_Pervasives_Native.Some _68099)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68104)::(t1,uu____68106)::(tacopt,uu____68108)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____68153 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68153
                 (fun e1  ->
                    let uu____68159 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____68159
                      (fun t2  ->
                         let uu____68165 =
                           let uu____68170 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68170 tacopt  in
                         FStar_Util.bind_opt uu____68165
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68185  ->
                                   FStar_Pervasives_Native.Some _68185)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68190)::(c,uu____68192)::(tacopt,uu____68194)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____68239 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68239
                 (fun e1  ->
                    let uu____68245 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____68245
                      (fun c1  ->
                         let uu____68251 =
                           let uu____68256 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68256 tacopt  in
                         FStar_Util.bind_opt uu____68251
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68271  ->
                                   FStar_Pervasives_Native.Some _68271)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _68291  -> FStar_Pervasives_Native.Some _68291)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____68292 ->
               (if w
                then
                  (let uu____68307 =
                     let uu____68313 =
                       let uu____68315 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____68315
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____68313)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____68307)
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
    let uu____68344 =
      let uu____68349 =
        let uu____68350 =
          let uu____68359 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____68359  in
        let uu____68361 =
          let uu____68372 =
            let uu____68381 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____68381  in
          let uu____68382 =
            let uu____68393 =
              let uu____68402 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____68402  in
            [uu____68393]  in
          uu____68372 :: uu____68382  in
        uu____68350 :: uu____68361  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____68349
       in
    uu____68344 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68455 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68455 with
    | (hd1,args) ->
        let uu____68500 =
          let uu____68513 =
            let uu____68514 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68514.FStar_Syntax_Syntax.n  in
          (uu____68513, args)  in
        (match uu____68500 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____68529)::(idx,uu____68531)::(s,uu____68533)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____68578 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____68578
               (fun nm1  ->
                  let uu____68588 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____68588
                    (fun idx1  ->
                       let uu____68594 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____68594
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _68601  ->
                                 FStar_Pervasives_Native.Some _68601)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____68602 ->
             (if w
              then
                (let uu____68617 =
                   let uu____68623 =
                     let uu____68625 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____68625
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____68623)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____68617)
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
        let uu____68651 =
          let uu____68656 =
            let uu____68657 =
              let uu____68666 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____68666  in
            let uu____68667 =
              let uu____68678 =
                let uu____68687 =
                  let uu____68688 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____68688 rng md  in
                FStar_Syntax_Syntax.as_arg uu____68687  in
              [uu____68678]  in
            uu____68657 :: uu____68667  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____68656
           in
        uu____68651 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____68726 =
          let uu____68731 =
            let uu____68732 =
              let uu____68741 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____68741  in
            let uu____68742 =
              let uu____68753 =
                let uu____68762 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____68762  in
              [uu____68753]  in
            uu____68732 :: uu____68742  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____68731
           in
        uu____68726 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_68789 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_68789.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_68789.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68808 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68808 with
    | (hd1,args) ->
        let uu____68853 =
          let uu____68866 =
            let uu____68867 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68867.FStar_Syntax_Syntax.n  in
          (uu____68866, args)  in
        (match uu____68853 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____68882)::(md,uu____68884)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____68919 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____68919
               (fun t3  ->
                  let uu____68925 =
                    let uu____68930 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____68930 md  in
                  FStar_Util.bind_opt uu____68925
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _68945  -> FStar_Pervasives_Native.Some _68945)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____68950)::(post,uu____68952)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____68987 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____68987
               (fun pre1  ->
                  let uu____68993 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____68993
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _69000  -> FStar_Pervasives_Native.Some _69000)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _69018  -> FStar_Pervasives_Native.Some _69018)
               FStar_Reflection_Data.C_Unknown
         | uu____69019 ->
             (if w
              then
                (let uu____69034 =
                   let uu____69040 =
                     let uu____69042 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____69042
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69040)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69034)
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
    let uu___1175_69067 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_69067.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_69067.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69088 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69088 with
    | (hd1,args) ->
        let uu____69133 =
          let uu____69148 =
            let uu____69149 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69149.FStar_Syntax_Syntax.n  in
          (uu____69148, args)  in
        (match uu____69133 with
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
         | uu____69221 ->
             (if w
              then
                (let uu____69238 =
                   let uu____69244 =
                     let uu____69246 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____69246
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69244)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69238)
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
    let uu____69283 =
      let uu____69284 = FStar_Syntax_Subst.compress t  in
      uu____69284.FStar_Syntax_Syntax.n  in
    match uu____69283 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____69290;
          FStar_Syntax_Syntax.rng = uu____69291;_}
        ->
        let uu____69294 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____69294
    | uu____69295 ->
        (if w
         then
           (let uu____69298 =
              let uu____69304 =
                let uu____69306 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____69306
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____69304)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69298)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____69366 uu____69367 =
    let uu____69389 =
      let uu____69395 = FStar_Ident.range_of_id i  in
      let uu____69396 = FStar_Ident.text_of_id i  in
      (uu____69395, uu____69396)  in
    embed repr rng uu____69389  in
  let unembed_ident t w uu____69424 =
    let uu____69430 = unembed' w repr t  in
    match uu____69430 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____69454 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____69454
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____69461 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____69461
  
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
        let uu____69500 =
          let uu____69505 =
            let uu____69506 =
              let uu____69515 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____69515  in
            let uu____69517 =
              let uu____69528 =
                let uu____69537 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____69537  in
              let uu____69538 =
                let uu____69549 =
                  let uu____69558 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____69558  in
                let uu____69561 =
                  let uu____69572 =
                    let uu____69581 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____69581  in
                  let uu____69582 =
                    let uu____69593 =
                      let uu____69602 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____69602  in
                    [uu____69593]  in
                  uu____69572 :: uu____69582  in
                uu____69549 :: uu____69561  in
              uu____69528 :: uu____69538  in
            uu____69506 :: uu____69517  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____69505
           in
        uu____69500 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____69655 =
          let uu____69660 =
            let uu____69661 =
              let uu____69670 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69670  in
            let uu____69674 =
              let uu____69685 =
                let uu____69694 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____69694  in
              [uu____69685]  in
            uu____69661 :: uu____69674  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____69660
           in
        uu____69655 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____69738 =
          let uu____69743 =
            let uu____69744 =
              let uu____69753 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69753  in
            let uu____69757 =
              let uu____69768 =
                let uu____69777 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____69777  in
              let uu____69780 =
                let uu____69791 =
                  let uu____69800 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____69800  in
                let uu____69801 =
                  let uu____69812 =
                    let uu____69821 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____69821  in
                  let uu____69822 =
                    let uu____69833 =
                      let uu____69842 =
                        let uu____69843 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____69843 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____69842  in
                    [uu____69833]  in
                  uu____69812 :: uu____69822  in
                uu____69791 :: uu____69801  in
              uu____69768 :: uu____69780  in
            uu____69744 :: uu____69757  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____69743
           in
        uu____69738 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_69909 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_69909.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_69909.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69928 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69928 with
    | (hd1,args) ->
        let uu____69973 =
          let uu____69986 =
            let uu____69987 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69987.FStar_Syntax_Syntax.n  in
          (uu____69986, args)  in
        (match uu____69973 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____70002)::(us,uu____70004)::(bs,uu____70006)::
            (t2,uu____70008)::(dcs,uu____70010)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____70075 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____70075
               (fun nm1  ->
                  let uu____70093 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____70093
                    (fun us1  ->
                       let uu____70107 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____70107
                         (fun bs1  ->
                            let uu____70113 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____70113
                              (fun t3  ->
                                 let uu____70119 =
                                   let uu____70127 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____70127 dcs  in
                                 FStar_Util.bind_opt uu____70119
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _70157  ->
                                           FStar_Pervasives_Native.Some
                                             _70157)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____70166)::(fvar1,uu____70168)::(univs1,uu____70170)::
            (ty,uu____70172)::(t2,uu____70174)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____70239 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____70239
               (fun r1  ->
                  let uu____70249 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____70249
                    (fun fvar2  ->
                       let uu____70255 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____70255
                         (fun univs2  ->
                            let uu____70269 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____70269
                              (fun ty1  ->
                                 let uu____70275 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____70275
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _70282  ->
                                           FStar_Pervasives_Native.Some
                                             _70282)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____70301 ->
             (if w
              then
                (let uu____70316 =
                   let uu____70322 =
                     let uu____70324 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____70324
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70322)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70316)
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
          let uu____70350 =
            let uu____70355 =
              let uu____70356 =
                let uu____70365 =
                  let uu____70366 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____70366  in
                FStar_Syntax_Syntax.as_arg uu____70365  in
              [uu____70356]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____70355
             in
          uu____70350 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____70388 =
            let uu____70393 =
              let uu____70394 =
                let uu____70403 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____70403  in
              let uu____70404 =
                let uu____70415 =
                  let uu____70424 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____70424  in
                [uu____70415]  in
              uu____70394 :: uu____70404  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____70393
             in
          uu____70388 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_70451 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_70451.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_70451.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____70472 = FStar_Syntax_Util.head_and_args t1  in
    match uu____70472 with
    | (hd1,args) ->
        let uu____70517 =
          let uu____70530 =
            let uu____70531 = FStar_Syntax_Util.un_uinst hd1  in
            uu____70531.FStar_Syntax_Syntax.n  in
          (uu____70530, args)  in
        (match uu____70517 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____70561)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____70586 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____70586
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _70593  -> FStar_Pervasives_Native.Some _70593)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____70596)::(e2,uu____70598)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____70633 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____70633
               (fun e11  ->
                  let uu____70639 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____70639
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _70646  -> FStar_Pervasives_Native.Some _70646)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____70647 ->
             (if w
              then
                (let uu____70662 =
                   let uu____70668 =
                     let uu____70670 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____70670
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70668)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70662)
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
    let uu____70694 =
      let uu____70699 =
        let uu____70700 =
          let uu____70709 =
            let uu____70710 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____70710  in
          FStar_Syntax_Syntax.as_arg uu____70709  in
        [uu____70700]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____70699
       in
    uu____70694 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70736 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____70736 with
    | (bv,aq) ->
        let uu____70743 =
          let uu____70748 =
            let uu____70749 =
              let uu____70758 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____70758  in
            let uu____70759 =
              let uu____70770 =
                let uu____70779 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____70779  in
              [uu____70770]  in
            uu____70749 :: uu____70759  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____70748
           in
        uu____70743 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70813 =
      let uu____70818 =
        let uu____70819 =
          let uu____70828 =
            let uu____70829 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____70836 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____70829 i.FStar_Syntax_Syntax.rng uu____70836  in
          FStar_Syntax_Syntax.as_arg uu____70828  in
        [uu____70819]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____70818
       in
    uu____70813 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70868 =
      let uu____70873 =
        let uu____70874 =
          let uu____70883 =
            let uu____70884 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____70884  in
          FStar_Syntax_Syntax.as_arg uu____70883  in
        [uu____70874]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____70873
       in
    uu____70868 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70916 =
      let uu____70921 =
        let uu____70922 =
          let uu____70931 =
            let uu____70932 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____70932  in
          FStar_Syntax_Syntax.as_arg uu____70931  in
        [uu____70922]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____70921
       in
    uu____70916 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  