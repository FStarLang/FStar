open Prims
let mk_emb :
  'Auu____64269 .
    (FStar_Range.range -> 'Auu____64269 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____64269 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____64269 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____64313 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____64313
  
let embed :
  'Auu____64361 .
    'Auu____64361 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____64361 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____64381 = FStar_Syntax_Embeddings.embed e x  in
        uu____64381 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____64422 .
    Prims.bool ->
      'Auu____64422 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____64422 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____64446 = FStar_Syntax_Embeddings.unembed e x  in
        uu____64446 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____64488 =
      let uu____64489 = FStar_Syntax_Subst.compress t  in
      uu____64489.FStar_Syntax_Syntax.n  in
    match uu____64488 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____64495;
          FStar_Syntax_Syntax.rng = uu____64496;_}
        ->
        let uu____64499 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64499
    | uu____64500 ->
        (if w
         then
           (let uu____64503 =
              let uu____64509 =
                let uu____64511 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____64511  in
              (FStar_Errors.Warning_NotEmbedded, uu____64509)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64503)
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
    let uu____64548 =
      let uu____64549 = FStar_Syntax_Subst.compress t  in
      uu____64549.FStar_Syntax_Syntax.n  in
    match uu____64548 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____64555;
          FStar_Syntax_Syntax.rng = uu____64556;_}
        ->
        let uu____64559 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64559
    | uu____64560 ->
        (if w
         then
           (let uu____64563 =
              let uu____64569 =
                let uu____64571 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____64571
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64569)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64563)
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
          let uu____64623 = f x  in
          FStar_Util.bind_opt uu____64623
            (fun x1  ->
               let uu____64631 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64631
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
        let uu____64700 =
          mapM_opt
            (fun uu____64713  ->
               match uu____64713 with
               | (bv,e) ->
                   let uu____64722 = unembed_term w e  in
                   FStar_Util.bind_opt uu____64722
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____64700
          (fun s  ->
             let uu____64736 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____64736)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____64738 =
        let uu____64739 = FStar_Syntax_Subst.compress t1  in
        uu____64739.FStar_Syntax_Syntax.n  in
      match uu____64738 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____64750 ->
          (if w
           then
             (let uu____64753 =
                let uu____64759 =
                  let uu____64761 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____64761
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____64759)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____64753)
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
          let uu____64796 =
            let uu____64801 =
              let uu____64802 =
                let uu____64811 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____64811  in
              [uu____64802]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____64801
             in
          uu____64796 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_64830 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_64830.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_64830.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64851 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64851 with
    | (hd1,args) ->
        let uu____64896 =
          let uu____64911 =
            let uu____64912 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64912.FStar_Syntax_Syntax.n  in
          (uu____64911, args)  in
        (match uu____64896 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____64967)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____65002 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____65002
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____65007 ->
             (if w
              then
                (let uu____65024 =
                   let uu____65030 =
                     let uu____65032 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____65032
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65030)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65024)
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
    let uu____65072 =
      let uu____65073 = FStar_Syntax_Subst.compress t  in
      uu____65073.FStar_Syntax_Syntax.n  in
    match uu____65072 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____65079;
          FStar_Syntax_Syntax.rng = uu____65080;_}
        ->
        let uu____65083 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65083
    | uu____65084 ->
        (if w
         then
           (let uu____65087 =
              let uu____65093 =
                let uu____65095 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____65095  in
              (FStar_Errors.Warning_NotEmbedded, uu____65093)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65087)
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
    let uu____65132 =
      let uu____65133 = FStar_Syntax_Subst.compress t  in
      uu____65133.FStar_Syntax_Syntax.n  in
    match uu____65132 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____65139;
          FStar_Syntax_Syntax.rng = uu____65140;_}
        ->
        let uu____65143 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65143
    | uu____65144 ->
        (if w
         then
           (let uu____65147 =
              let uu____65153 =
                let uu____65155 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____65155  in
              (FStar_Errors.Warning_NotEmbedded, uu____65153)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65147)
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
    let uu____65192 =
      let uu____65193 = FStar_Syntax_Subst.compress t  in
      uu____65193.FStar_Syntax_Syntax.n  in
    match uu____65192 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____65199;
          FStar_Syntax_Syntax.rng = uu____65200;_}
        ->
        let uu____65203 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65203
    | uu____65204 ->
        (if w
         then
           (let uu____65207 =
              let uu____65213 =
                let uu____65215 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____65215  in
              (FStar_Errors.Warning_NotEmbedded, uu____65213)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65207)
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
          let uu____65241 =
            let uu____65246 =
              let uu____65247 =
                let uu____65256 =
                  let uu____65257 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65257  in
                FStar_Syntax_Syntax.as_arg uu____65256  in
              [uu____65247]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____65246
             in
          uu____65241 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____65279 =
            let uu____65284 =
              let uu____65285 =
                let uu____65294 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____65294  in
              [uu____65285]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____65284
             in
          uu____65279 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____65315 =
            let uu____65320 =
              let uu____65321 =
                let uu____65330 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____65330  in
              [uu____65321]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____65320
             in
          uu____65315 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____65350 =
            let uu____65355 =
              let uu____65356 =
                let uu____65365 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____65365  in
              [uu____65356]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____65355
             in
          uu____65350 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_65387 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_65387.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_65387.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65408 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65408 with
    | (hd1,args) ->
        let uu____65453 =
          let uu____65468 =
            let uu____65469 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65469.FStar_Syntax_Syntax.n  in
          (uu____65468, args)  in
        (match uu____65453 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65543)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____65578 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65578
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65585  -> FStar_Pervasives_Native.Some _65585)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____65588)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____65623 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____65623
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _65634  -> FStar_Pervasives_Native.Some _65634)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____65637)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____65672 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____65672
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _65679  -> FStar_Pervasives_Native.Some _65679)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _65701  -> FStar_Pervasives_Native.Some _65701)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____65704)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____65739 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____65739
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _65758  -> FStar_Pervasives_Native.Some _65758)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____65759 ->
             (if w
              then
                (let uu____65776 =
                   let uu____65782 =
                     let uu____65784 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____65784
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65782)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65776)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____65797  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65810 =
            let uu____65815 =
              let uu____65816 =
                let uu____65825 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____65825  in
              [uu____65816]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____65815
             in
          uu____65810 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65850 =
            let uu____65855 =
              let uu____65856 =
                let uu____65865 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____65865  in
              let uu____65866 =
                let uu____65877 =
                  let uu____65886 =
                    let uu____65887 =
                      let uu____65892 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____65892  in
                    embed uu____65887 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____65886  in
                [uu____65877]  in
              uu____65856 :: uu____65866  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____65855
             in
          uu____65850 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65924 =
            let uu____65929 =
              let uu____65930 =
                let uu____65939 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65939  in
              [uu____65930]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____65929
             in
          uu____65924 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65959 =
            let uu____65964 =
              let uu____65965 =
                let uu____65974 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65974  in
              [uu____65965]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____65964
             in
          uu____65959 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65995 =
            let uu____66000 =
              let uu____66001 =
                let uu____66010 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66010  in
              let uu____66011 =
                let uu____66022 =
                  let uu____66031 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____66031  in
                [uu____66022]  in
              uu____66001 :: uu____66011  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____66000
             in
          uu____65995 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____66076 = FStar_Syntax_Util.head_and_args t1  in
      match uu____66076 with
      | (hd1,args) ->
          let uu____66121 =
            let uu____66134 =
              let uu____66135 = FStar_Syntax_Util.un_uinst hd1  in
              uu____66135.FStar_Syntax_Syntax.n  in
            (uu____66134, args)  in
          (match uu____66121 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____66150)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____66175 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____66175
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _66182  -> FStar_Pervasives_Native.Some _66182)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____66185)::(ps,uu____66187)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____66222 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____66222
                 (fun f1  ->
                    let uu____66228 =
                      let uu____66233 =
                        let uu____66238 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____66238  in
                      unembed' w uu____66233 ps  in
                    FStar_Util.bind_opt uu____66228
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _66251  ->
                              FStar_Pervasives_Native.Some _66251)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66256)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____66281 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66281
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66288  -> FStar_Pervasives_Native.Some _66288)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66291)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____66316 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66316
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66323  -> FStar_Pervasives_Native.Some _66323)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____66326)::(t2,uu____66328)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____66363 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66363
                 (fun bv1  ->
                    let uu____66369 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____66369
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _66376  ->
                              FStar_Pervasives_Native.Some _66376)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____66377 ->
               (if w
                then
                  (let uu____66392 =
                     let uu____66398 =
                       let uu____66400 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____66400
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____66398)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____66392)
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
    let uu____66427 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____66427
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____66442 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____66442 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____66465 =
            let uu____66470 =
              let uu____66471 =
                let uu____66480 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66480  in
              [uu____66471]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____66470
             in
          uu____66465 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____66500 =
            let uu____66505 =
              let uu____66506 =
                let uu____66515 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66515  in
              [uu____66506]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____66505
             in
          uu____66500 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____66535 =
            let uu____66540 =
              let uu____66541 =
                let uu____66550 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66550  in
              [uu____66541]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____66540
             in
          uu____66535 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66571 =
            let uu____66576 =
              let uu____66577 =
                let uu____66586 =
                  let uu____66587 = e_term_aq aq  in
                  embed uu____66587 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____66586  in
              let uu____66590 =
                let uu____66601 =
                  let uu____66610 =
                    let uu____66611 = e_argv_aq aq  in
                    embed uu____66611 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____66610  in
                [uu____66601]  in
              uu____66577 :: uu____66590  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____66576
             in
          uu____66571 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____66650 =
            let uu____66655 =
              let uu____66656 =
                let uu____66665 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66665  in
              let uu____66666 =
                let uu____66677 =
                  let uu____66686 =
                    let uu____66687 = e_term_aq aq  in
                    embed uu____66687 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66686  in
                [uu____66677]  in
              uu____66656 :: uu____66666  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____66655
             in
          uu____66650 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66718 =
            let uu____66723 =
              let uu____66724 =
                let uu____66733 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66733  in
              let uu____66734 =
                let uu____66745 =
                  let uu____66754 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____66754  in
                [uu____66745]  in
              uu____66724 :: uu____66734  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____66723
             in
          uu____66718 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66782 =
            let uu____66787 =
              let uu____66788 =
                let uu____66797 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____66797  in
              [uu____66788]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____66787
             in
          uu____66782 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____66818 =
            let uu____66823 =
              let uu____66824 =
                let uu____66833 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66833  in
              let uu____66834 =
                let uu____66845 =
                  let uu____66854 =
                    let uu____66855 = e_term_aq aq  in
                    embed uu____66855 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66854  in
                [uu____66845]  in
              uu____66824 :: uu____66834  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____66823
             in
          uu____66818 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66885 =
            let uu____66890 =
              let uu____66891 =
                let uu____66900 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____66900  in
              [uu____66891]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____66890
             in
          uu____66885 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66921 =
            let uu____66926 =
              let uu____66927 =
                let uu____66936 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____66936  in
              let uu____66937 =
                let uu____66948 =
                  let uu____66957 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____66957  in
                [uu____66948]  in
              uu____66927 :: uu____66937  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____66926
             in
          uu____66921 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66994 =
            let uu____66999 =
              let uu____67000 =
                let uu____67009 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____67009  in
              let uu____67011 =
                let uu____67022 =
                  let uu____67031 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____67031  in
                let uu____67032 =
                  let uu____67043 =
                    let uu____67052 =
                      let uu____67053 = e_term_aq aq  in
                      embed uu____67053 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____67052  in
                  let uu____67056 =
                    let uu____67067 =
                      let uu____67076 =
                        let uu____67077 = e_term_aq aq  in
                        embed uu____67077 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____67076  in
                    [uu____67067]  in
                  uu____67043 :: uu____67056  in
                uu____67022 :: uu____67032  in
              uu____67000 :: uu____67011  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____66999
             in
          uu____66994 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____67128 =
            let uu____67133 =
              let uu____67134 =
                let uu____67143 =
                  let uu____67144 = e_term_aq aq  in embed uu____67144 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____67143  in
              let uu____67147 =
                let uu____67158 =
                  let uu____67167 =
                    let uu____67168 =
                      let uu____67177 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____67177  in
                    embed uu____67168 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____67167  in
                [uu____67158]  in
              uu____67134 :: uu____67147  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____67133
             in
          uu____67128 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____67227 =
            let uu____67232 =
              let uu____67233 =
                let uu____67242 =
                  let uu____67243 = e_term_aq aq  in embed uu____67243 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67242  in
              let uu____67246 =
                let uu____67257 =
                  let uu____67266 =
                    let uu____67267 = e_term_aq aq  in
                    embed uu____67267 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____67266  in
                let uu____67270 =
                  let uu____67281 =
                    let uu____67290 =
                      let uu____67291 =
                        let uu____67296 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67296  in
                      embed uu____67291 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67290  in
                  [uu____67281]  in
                uu____67257 :: uu____67270  in
              uu____67233 :: uu____67246  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____67232
             in
          uu____67227 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____67342 =
            let uu____67347 =
              let uu____67348 =
                let uu____67357 =
                  let uu____67358 = e_term_aq aq  in embed uu____67358 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67357  in
              let uu____67361 =
                let uu____67372 =
                  let uu____67381 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____67381  in
                let uu____67382 =
                  let uu____67393 =
                    let uu____67402 =
                      let uu____67403 =
                        let uu____67408 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67408  in
                      embed uu____67403 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67402  in
                  [uu____67393]  in
                uu____67372 :: uu____67382  in
              uu____67348 :: uu____67361  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____67347
             in
          uu____67342 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_67447 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_67447.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_67447.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____67465 = FStar_Syntax_Util.head_and_args t  in
      match uu____67465 with
      | (hd1,args) ->
          let uu____67510 =
            let uu____67523 =
              let uu____67524 = FStar_Syntax_Util.un_uinst hd1  in
              uu____67524.FStar_Syntax_Syntax.n  in
            (uu____67523, args)  in
          (match uu____67510 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67539)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____67564 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67564
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67571  -> FStar_Pervasives_Native.Some _67571)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67574)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____67599 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67599
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67606  -> FStar_Pervasives_Native.Some _67606)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____67609)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____67634 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____67634
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _67641  -> FStar_Pervasives_Native.Some _67641)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____67644)::(r,uu____67646)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____67681 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____67681
                 (fun l1  ->
                    let uu____67687 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____67687
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _67694  ->
                              FStar_Pervasives_Native.Some _67694)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67697)::(t1,uu____67699)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____67734 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67734
                 (fun b1  ->
                    let uu____67740 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67740
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67747  ->
                              FStar_Pervasives_Native.Some _67747)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67750)::(t1,uu____67752)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____67787 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67787
                 (fun b1  ->
                    let uu____67793 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____67793
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _67800  ->
                              FStar_Pervasives_Native.Some _67800)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____67803)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____67828 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____67828
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _67835  -> FStar_Pervasives_Native.Some _67835)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67838)::(t1,uu____67840)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____67875 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67875
                 (fun b1  ->
                    let uu____67881 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67881
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67888  ->
                              FStar_Pervasives_Native.Some _67888)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____67891)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____67916 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____67916
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _67923  -> FStar_Pervasives_Native.Some _67923)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____67926)::(l,uu____67928)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____67963 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____67963
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _67972  -> FStar_Pervasives_Native.Some _67972)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____67975)::(b,uu____67977)::(t1,uu____67979)::
              (t2,uu____67981)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____68036 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____68036
                 (fun r1  ->
                    let uu____68046 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____68046
                      (fun b1  ->
                         let uu____68052 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____68052
                           (fun t11  ->
                              let uu____68058 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____68058
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _68065  ->
                                        FStar_Pervasives_Native.Some _68065)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____68069)::(brs,uu____68071)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____68106 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____68106
                 (fun t2  ->
                    let uu____68112 =
                      let uu____68117 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____68117 brs  in
                    FStar_Util.bind_opt uu____68112
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _68132  ->
                              FStar_Pervasives_Native.Some _68132)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68137)::(t1,uu____68139)::(tacopt,uu____68141)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____68186 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68186
                 (fun e1  ->
                    let uu____68192 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____68192
                      (fun t2  ->
                         let uu____68198 =
                           let uu____68203 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68203 tacopt  in
                         FStar_Util.bind_opt uu____68198
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68218  ->
                                   FStar_Pervasives_Native.Some _68218)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68223)::(c,uu____68225)::(tacopt,uu____68227)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____68272 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68272
                 (fun e1  ->
                    let uu____68278 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____68278
                      (fun c1  ->
                         let uu____68284 =
                           let uu____68289 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68289 tacopt  in
                         FStar_Util.bind_opt uu____68284
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68304  ->
                                   FStar_Pervasives_Native.Some _68304)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _68324  -> FStar_Pervasives_Native.Some _68324)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____68325 ->
               (if w
                then
                  (let uu____68340 =
                     let uu____68346 =
                       let uu____68348 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____68348
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____68346)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____68340)
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
    let uu____68377 =
      let uu____68382 =
        let uu____68383 =
          let uu____68392 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____68392  in
        let uu____68394 =
          let uu____68405 =
            let uu____68414 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____68414  in
          let uu____68415 =
            let uu____68426 =
              let uu____68435 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____68435  in
            [uu____68426]  in
          uu____68405 :: uu____68415  in
        uu____68383 :: uu____68394  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____68382
       in
    uu____68377 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68488 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68488 with
    | (hd1,args) ->
        let uu____68533 =
          let uu____68546 =
            let uu____68547 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68547.FStar_Syntax_Syntax.n  in
          (uu____68546, args)  in
        (match uu____68533 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____68562)::(idx,uu____68564)::(s,uu____68566)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____68611 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____68611
               (fun nm1  ->
                  let uu____68621 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____68621
                    (fun idx1  ->
                       let uu____68627 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____68627
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _68634  ->
                                 FStar_Pervasives_Native.Some _68634)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____68635 ->
             (if w
              then
                (let uu____68650 =
                   let uu____68656 =
                     let uu____68658 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____68658
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____68656)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____68650)
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
        let uu____68684 =
          let uu____68689 =
            let uu____68690 =
              let uu____68699 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____68699  in
            let uu____68700 =
              let uu____68711 =
                let uu____68720 =
                  let uu____68721 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____68721 rng md  in
                FStar_Syntax_Syntax.as_arg uu____68720  in
              [uu____68711]  in
            uu____68690 :: uu____68700  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____68689
           in
        uu____68684 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____68759 =
          let uu____68764 =
            let uu____68765 =
              let uu____68774 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____68774  in
            let uu____68775 =
              let uu____68786 =
                let uu____68795 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____68795  in
              [uu____68786]  in
            uu____68765 :: uu____68775  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____68764
           in
        uu____68759 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_68822 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_68822.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_68822.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68841 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68841 with
    | (hd1,args) ->
        let uu____68886 =
          let uu____68899 =
            let uu____68900 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68900.FStar_Syntax_Syntax.n  in
          (uu____68899, args)  in
        (match uu____68886 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____68915)::(md,uu____68917)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____68952 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____68952
               (fun t3  ->
                  let uu____68958 =
                    let uu____68963 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____68963 md  in
                  FStar_Util.bind_opt uu____68958
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _68978  -> FStar_Pervasives_Native.Some _68978)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____68983)::(post,uu____68985)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____69020 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____69020
               (fun pre1  ->
                  let uu____69026 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____69026
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _69033  -> FStar_Pervasives_Native.Some _69033)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _69051  -> FStar_Pervasives_Native.Some _69051)
               FStar_Reflection_Data.C_Unknown
         | uu____69052 ->
             (if w
              then
                (let uu____69067 =
                   let uu____69073 =
                     let uu____69075 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____69075
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69073)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69067)
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
    let uu___1175_69100 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_69100.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_69100.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69121 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69121 with
    | (hd1,args) ->
        let uu____69166 =
          let uu____69181 =
            let uu____69182 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69182.FStar_Syntax_Syntax.n  in
          (uu____69181, args)  in
        (match uu____69166 with
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
         | uu____69254 ->
             (if w
              then
                (let uu____69271 =
                   let uu____69277 =
                     let uu____69279 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____69279
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69277)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69271)
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
    let uu____69316 =
      let uu____69317 = FStar_Syntax_Subst.compress t  in
      uu____69317.FStar_Syntax_Syntax.n  in
    match uu____69316 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____69323;
          FStar_Syntax_Syntax.rng = uu____69324;_}
        ->
        let uu____69327 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____69327
    | uu____69328 ->
        (if w
         then
           (let uu____69331 =
              let uu____69337 =
                let uu____69339 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____69339
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____69337)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69331)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____69399 uu____69400 =
    let uu____69422 =
      let uu____69428 = FStar_Ident.range_of_id i  in
      let uu____69429 = FStar_Ident.text_of_id i  in
      (uu____69428, uu____69429)  in
    embed repr rng uu____69422  in
  let unembed_ident t w uu____69457 =
    let uu____69463 = unembed' w repr t  in
    match uu____69463 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____69487 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____69487
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____69494 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____69494
  
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
        let uu____69533 =
          let uu____69538 =
            let uu____69539 =
              let uu____69548 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____69548  in
            let uu____69550 =
              let uu____69561 =
                let uu____69570 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____69570  in
              let uu____69571 =
                let uu____69582 =
                  let uu____69591 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____69591  in
                let uu____69594 =
                  let uu____69605 =
                    let uu____69614 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____69614  in
                  let uu____69615 =
                    let uu____69626 =
                      let uu____69635 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____69635  in
                    [uu____69626]  in
                  uu____69605 :: uu____69615  in
                uu____69582 :: uu____69594  in
              uu____69561 :: uu____69571  in
            uu____69539 :: uu____69550  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____69538
           in
        uu____69533 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____69688 =
          let uu____69693 =
            let uu____69694 =
              let uu____69703 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69703  in
            let uu____69707 =
              let uu____69718 =
                let uu____69727 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____69727  in
              [uu____69718]  in
            uu____69694 :: uu____69707  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____69693
           in
        uu____69688 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____69771 =
          let uu____69776 =
            let uu____69777 =
              let uu____69786 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69786  in
            let uu____69790 =
              let uu____69801 =
                let uu____69810 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____69810  in
              let uu____69813 =
                let uu____69824 =
                  let uu____69833 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____69833  in
                let uu____69834 =
                  let uu____69845 =
                    let uu____69854 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____69854  in
                  let uu____69855 =
                    let uu____69866 =
                      let uu____69875 =
                        let uu____69876 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____69876 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____69875  in
                    [uu____69866]  in
                  uu____69845 :: uu____69855  in
                uu____69824 :: uu____69834  in
              uu____69801 :: uu____69813  in
            uu____69777 :: uu____69790  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____69776
           in
        uu____69771 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_69942 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_69942.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_69942.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69961 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69961 with
    | (hd1,args) ->
        let uu____70006 =
          let uu____70019 =
            let uu____70020 = FStar_Syntax_Util.un_uinst hd1  in
            uu____70020.FStar_Syntax_Syntax.n  in
          (uu____70019, args)  in
        (match uu____70006 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____70035)::(us,uu____70037)::(bs,uu____70039)::
            (t2,uu____70041)::(dcs,uu____70043)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____70108 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____70108
               (fun nm1  ->
                  let uu____70126 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____70126
                    (fun us1  ->
                       let uu____70140 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____70140
                         (fun bs1  ->
                            let uu____70146 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____70146
                              (fun t3  ->
                                 let uu____70152 =
                                   let uu____70160 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____70160 dcs  in
                                 FStar_Util.bind_opt uu____70152
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _70190  ->
                                           FStar_Pervasives_Native.Some
                                             _70190)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____70199)::(fvar1,uu____70201)::(univs1,uu____70203)::
            (ty,uu____70205)::(t2,uu____70207)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____70272 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____70272
               (fun r1  ->
                  let uu____70282 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____70282
                    (fun fvar2  ->
                       let uu____70288 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____70288
                         (fun univs2  ->
                            let uu____70302 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____70302
                              (fun ty1  ->
                                 let uu____70308 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____70308
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _70315  ->
                                           FStar_Pervasives_Native.Some
                                             _70315)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____70334 ->
             (if w
              then
                (let uu____70349 =
                   let uu____70355 =
                     let uu____70357 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____70357
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70355)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70349)
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
          let uu____70383 =
            let uu____70388 =
              let uu____70389 =
                let uu____70398 =
                  let uu____70399 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____70399  in
                FStar_Syntax_Syntax.as_arg uu____70398  in
              [uu____70389]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____70388
             in
          uu____70383 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____70421 =
            let uu____70426 =
              let uu____70427 =
                let uu____70436 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____70436  in
              let uu____70437 =
                let uu____70448 =
                  let uu____70457 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____70457  in
                [uu____70448]  in
              uu____70427 :: uu____70437  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____70426
             in
          uu____70421 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_70484 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_70484.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_70484.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____70505 = FStar_Syntax_Util.head_and_args t1  in
    match uu____70505 with
    | (hd1,args) ->
        let uu____70550 =
          let uu____70563 =
            let uu____70564 = FStar_Syntax_Util.un_uinst hd1  in
            uu____70564.FStar_Syntax_Syntax.n  in
          (uu____70563, args)  in
        (match uu____70550 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____70594)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____70619 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____70619
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _70626  -> FStar_Pervasives_Native.Some _70626)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____70629)::(e2,uu____70631)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____70666 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____70666
               (fun e11  ->
                  let uu____70672 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____70672
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _70679  -> FStar_Pervasives_Native.Some _70679)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____70680 ->
             (if w
              then
                (let uu____70695 =
                   let uu____70701 =
                     let uu____70703 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____70703
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70701)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70695)
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
    let uu____70727 =
      let uu____70732 =
        let uu____70733 =
          let uu____70742 =
            let uu____70743 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____70743  in
          FStar_Syntax_Syntax.as_arg uu____70742  in
        [uu____70733]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____70732
       in
    uu____70727 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70769 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____70769 with
    | (bv,aq) ->
        let uu____70776 =
          let uu____70781 =
            let uu____70782 =
              let uu____70791 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____70791  in
            let uu____70792 =
              let uu____70803 =
                let uu____70812 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____70812  in
              [uu____70803]  in
            uu____70782 :: uu____70792  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____70781
           in
        uu____70776 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70846 =
      let uu____70851 =
        let uu____70852 =
          let uu____70861 =
            let uu____70862 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____70869 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____70862 i.FStar_Syntax_Syntax.rng uu____70869  in
          FStar_Syntax_Syntax.as_arg uu____70861  in
        [uu____70852]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____70851
       in
    uu____70846 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70901 =
      let uu____70906 =
        let uu____70907 =
          let uu____70916 =
            let uu____70917 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____70917  in
          FStar_Syntax_Syntax.as_arg uu____70916  in
        [uu____70907]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____70906
       in
    uu____70901 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70949 =
      let uu____70954 =
        let uu____70955 =
          let uu____70964 =
            let uu____70965 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____70965  in
          FStar_Syntax_Syntax.as_arg uu____70964  in
        [uu____70955]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____70954
       in
    uu____70949 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  