open Prims
let mk_emb :
  'Auu____64241 .
    (FStar_Range.range -> 'Auu____64241 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____64241 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____64241 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____64285 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____64285
  
let embed :
  'Auu____64333 .
    'Auu____64333 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____64333 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____64353 = FStar_Syntax_Embeddings.embed e x  in
        uu____64353 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____64394 .
    Prims.bool ->
      'Auu____64394 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____64394 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____64418 = FStar_Syntax_Embeddings.unembed e x  in
        uu____64418 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____64460 =
      let uu____64461 = FStar_Syntax_Subst.compress t  in
      uu____64461.FStar_Syntax_Syntax.n  in
    match uu____64460 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____64467;
          FStar_Syntax_Syntax.rng = uu____64468;_}
        ->
        let uu____64471 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64471
    | uu____64472 ->
        (if w
         then
           (let uu____64475 =
              let uu____64481 =
                let uu____64483 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____64483  in
              (FStar_Errors.Warning_NotEmbedded, uu____64481)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64475)
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
    let uu____64520 =
      let uu____64521 = FStar_Syntax_Subst.compress t  in
      uu____64521.FStar_Syntax_Syntax.n  in
    match uu____64520 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____64527;
          FStar_Syntax_Syntax.rng = uu____64528;_}
        ->
        let uu____64531 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64531
    | uu____64532 ->
        (if w
         then
           (let uu____64535 =
              let uu____64541 =
                let uu____64543 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____64543
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64541)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64535)
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
          let uu____64595 = f x  in
          FStar_Util.bind_opt uu____64595
            (fun x1  ->
               let uu____64603 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64603
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
        let uu____64672 =
          mapM_opt
            (fun uu____64685  ->
               match uu____64685 with
               | (bv,e) ->
                   let uu____64694 = unembed_term w e  in
                   FStar_Util.bind_opt uu____64694
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____64672
          (fun s  ->
             let uu____64708 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____64708)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____64710 =
        let uu____64711 = FStar_Syntax_Subst.compress t1  in
        uu____64711.FStar_Syntax_Syntax.n  in
      match uu____64710 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____64722 ->
          (if w
           then
             (let uu____64725 =
                let uu____64731 =
                  let uu____64733 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____64733
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____64731)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____64725)
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
          let uu____64768 =
            let uu____64773 =
              let uu____64774 =
                let uu____64783 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____64783  in
              [uu____64774]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____64773
             in
          uu____64768 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_64802 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_64802.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_64802.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64823 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64823 with
    | (hd1,args) ->
        let uu____64868 =
          let uu____64883 =
            let uu____64884 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64884.FStar_Syntax_Syntax.n  in
          (uu____64883, args)  in
        (match uu____64868 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____64939)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____64974 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____64974
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____64979 ->
             (if w
              then
                (let uu____64996 =
                   let uu____65002 =
                     let uu____65004 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____65004
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65002)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64996)
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
    let uu____65044 =
      let uu____65045 = FStar_Syntax_Subst.compress t  in
      uu____65045.FStar_Syntax_Syntax.n  in
    match uu____65044 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____65051;
          FStar_Syntax_Syntax.rng = uu____65052;_}
        ->
        let uu____65055 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65055
    | uu____65056 ->
        (if w
         then
           (let uu____65059 =
              let uu____65065 =
                let uu____65067 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____65067  in
              (FStar_Errors.Warning_NotEmbedded, uu____65065)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65059)
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
    let uu____65104 =
      let uu____65105 = FStar_Syntax_Subst.compress t  in
      uu____65105.FStar_Syntax_Syntax.n  in
    match uu____65104 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____65111;
          FStar_Syntax_Syntax.rng = uu____65112;_}
        ->
        let uu____65115 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65115
    | uu____65116 ->
        (if w
         then
           (let uu____65119 =
              let uu____65125 =
                let uu____65127 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____65127  in
              (FStar_Errors.Warning_NotEmbedded, uu____65125)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65119)
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
    let uu____65164 =
      let uu____65165 = FStar_Syntax_Subst.compress t  in
      uu____65165.FStar_Syntax_Syntax.n  in
    match uu____65164 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____65171;
          FStar_Syntax_Syntax.rng = uu____65172;_}
        ->
        let uu____65175 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65175
    | uu____65176 ->
        (if w
         then
           (let uu____65179 =
              let uu____65185 =
                let uu____65187 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____65187  in
              (FStar_Errors.Warning_NotEmbedded, uu____65185)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____65179)
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
          let uu____65213 =
            let uu____65218 =
              let uu____65219 =
                let uu____65228 =
                  let uu____65229 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65229  in
                FStar_Syntax_Syntax.as_arg uu____65228  in
              [uu____65219]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____65218
             in
          uu____65213 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____65251 =
            let uu____65256 =
              let uu____65257 =
                let uu____65266 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____65266  in
              [uu____65257]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____65256
             in
          uu____65251 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____65287 =
            let uu____65292 =
              let uu____65293 =
                let uu____65302 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____65302  in
              [uu____65293]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____65292
             in
          uu____65287 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____65322 =
            let uu____65327 =
              let uu____65328 =
                let uu____65337 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____65337  in
              [uu____65328]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____65327
             in
          uu____65322 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_65359 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_65359.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_65359.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65380 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65380 with
    | (hd1,args) ->
        let uu____65425 =
          let uu____65440 =
            let uu____65441 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65441.FStar_Syntax_Syntax.n  in
          (uu____65440, args)  in
        (match uu____65425 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65515)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____65550 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65550
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65557  -> FStar_Pervasives_Native.Some _65557)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____65560)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____65595 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____65595
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _65606  -> FStar_Pervasives_Native.Some _65606)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____65609)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____65644 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____65644
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _65651  -> FStar_Pervasives_Native.Some _65651)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _65673  -> FStar_Pervasives_Native.Some _65673)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____65676)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____65711 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____65711
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _65730  -> FStar_Pervasives_Native.Some _65730)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____65731 ->
             (if w
              then
                (let uu____65748 =
                   let uu____65754 =
                     let uu____65756 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____65756
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65754)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65748)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____65769  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65782 =
            let uu____65787 =
              let uu____65788 =
                let uu____65797 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____65797  in
              [uu____65788]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____65787
             in
          uu____65782 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65822 =
            let uu____65827 =
              let uu____65828 =
                let uu____65837 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____65837  in
              let uu____65838 =
                let uu____65849 =
                  let uu____65858 =
                    let uu____65859 =
                      let uu____65864 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____65864  in
                    embed uu____65859 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____65858  in
                [uu____65849]  in
              uu____65828 :: uu____65838  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____65827
             in
          uu____65822 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65896 =
            let uu____65901 =
              let uu____65902 =
                let uu____65911 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65911  in
              [uu____65902]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____65901
             in
          uu____65896 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65931 =
            let uu____65936 =
              let uu____65937 =
                let uu____65946 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65946  in
              [uu____65937]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____65936
             in
          uu____65931 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65967 =
            let uu____65972 =
              let uu____65973 =
                let uu____65982 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____65982  in
              let uu____65983 =
                let uu____65994 =
                  let uu____66003 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____66003  in
                [uu____65994]  in
              uu____65973 :: uu____65983  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____65972
             in
          uu____65967 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____66048 = FStar_Syntax_Util.head_and_args t1  in
      match uu____66048 with
      | (hd1,args) ->
          let uu____66093 =
            let uu____66106 =
              let uu____66107 = FStar_Syntax_Util.un_uinst hd1  in
              uu____66107.FStar_Syntax_Syntax.n  in
            (uu____66106, args)  in
          (match uu____66093 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____66122)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____66147 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____66147
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _66154  -> FStar_Pervasives_Native.Some _66154)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____66157)::(ps,uu____66159)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____66194 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____66194
                 (fun f1  ->
                    let uu____66200 =
                      let uu____66205 =
                        let uu____66210 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____66210  in
                      unembed' w uu____66205 ps  in
                    FStar_Util.bind_opt uu____66200
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _66223  ->
                              FStar_Pervasives_Native.Some _66223)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66228)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____66253 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66253
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66260  -> FStar_Pervasives_Native.Some _66260)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____66263)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____66288 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66288
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _66295  -> FStar_Pervasives_Native.Some _66295)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____66298)::(t2,uu____66300)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____66335 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____66335
                 (fun bv1  ->
                    let uu____66341 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____66341
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _66348  ->
                              FStar_Pervasives_Native.Some _66348)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____66349 ->
               (if w
                then
                  (let uu____66364 =
                     let uu____66370 =
                       let uu____66372 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____66372
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____66370)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____66364)
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
    let uu____66399 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____66399
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____66414 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____66414 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____66437 =
            let uu____66442 =
              let uu____66443 =
                let uu____66452 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66452  in
              [uu____66443]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____66442
             in
          uu____66437 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____66472 =
            let uu____66477 =
              let uu____66478 =
                let uu____66487 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____66487  in
              [uu____66478]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____66477
             in
          uu____66472 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____66507 =
            let uu____66512 =
              let uu____66513 =
                let uu____66522 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66522  in
              [uu____66513]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____66512
             in
          uu____66507 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66543 =
            let uu____66548 =
              let uu____66549 =
                let uu____66558 =
                  let uu____66559 = e_term_aq aq  in
                  embed uu____66559 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____66558  in
              let uu____66562 =
                let uu____66573 =
                  let uu____66582 =
                    let uu____66583 = e_argv_aq aq  in
                    embed uu____66583 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____66582  in
                [uu____66573]  in
              uu____66549 :: uu____66562  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____66548
             in
          uu____66543 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____66622 =
            let uu____66627 =
              let uu____66628 =
                let uu____66637 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66637  in
              let uu____66638 =
                let uu____66649 =
                  let uu____66658 =
                    let uu____66659 = e_term_aq aq  in
                    embed uu____66659 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66658  in
                [uu____66649]  in
              uu____66628 :: uu____66638  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____66627
             in
          uu____66622 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66690 =
            let uu____66695 =
              let uu____66696 =
                let uu____66705 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____66705  in
              let uu____66706 =
                let uu____66717 =
                  let uu____66726 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____66726  in
                [uu____66717]  in
              uu____66696 :: uu____66706  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____66695
             in
          uu____66690 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66754 =
            let uu____66759 =
              let uu____66760 =
                let uu____66769 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____66769  in
              [uu____66760]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____66759
             in
          uu____66754 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____66790 =
            let uu____66795 =
              let uu____66796 =
                let uu____66805 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____66805  in
              let uu____66806 =
                let uu____66817 =
                  let uu____66826 =
                    let uu____66827 = e_term_aq aq  in
                    embed uu____66827 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____66826  in
                [uu____66817]  in
              uu____66796 :: uu____66806  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____66795
             in
          uu____66790 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66857 =
            let uu____66862 =
              let uu____66863 =
                let uu____66872 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____66872  in
              [uu____66863]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____66862
             in
          uu____66857 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66893 =
            let uu____66898 =
              let uu____66899 =
                let uu____66908 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____66908  in
              let uu____66909 =
                let uu____66920 =
                  let uu____66929 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____66929  in
                [uu____66920]  in
              uu____66899 :: uu____66909  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____66898
             in
          uu____66893 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66966 =
            let uu____66971 =
              let uu____66972 =
                let uu____66981 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____66981  in
              let uu____66983 =
                let uu____66994 =
                  let uu____67003 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____67003  in
                let uu____67004 =
                  let uu____67015 =
                    let uu____67024 =
                      let uu____67025 = e_term_aq aq  in
                      embed uu____67025 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____67024  in
                  let uu____67028 =
                    let uu____67039 =
                      let uu____67048 =
                        let uu____67049 = e_term_aq aq  in
                        embed uu____67049 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____67048  in
                    [uu____67039]  in
                  uu____67015 :: uu____67028  in
                uu____66994 :: uu____67004  in
              uu____66972 :: uu____66983  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____66971
             in
          uu____66966 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____67100 =
            let uu____67105 =
              let uu____67106 =
                let uu____67115 =
                  let uu____67116 = e_term_aq aq  in embed uu____67116 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____67115  in
              let uu____67119 =
                let uu____67130 =
                  let uu____67139 =
                    let uu____67140 =
                      let uu____67149 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____67149  in
                    embed uu____67140 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____67139  in
                [uu____67130]  in
              uu____67106 :: uu____67119  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____67105
             in
          uu____67100 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____67199 =
            let uu____67204 =
              let uu____67205 =
                let uu____67214 =
                  let uu____67215 = e_term_aq aq  in embed uu____67215 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67214  in
              let uu____67218 =
                let uu____67229 =
                  let uu____67238 =
                    let uu____67239 = e_term_aq aq  in
                    embed uu____67239 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____67238  in
                let uu____67242 =
                  let uu____67253 =
                    let uu____67262 =
                      let uu____67263 =
                        let uu____67268 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67268  in
                      embed uu____67263 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67262  in
                  [uu____67253]  in
                uu____67229 :: uu____67242  in
              uu____67205 :: uu____67218  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____67204
             in
          uu____67199 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____67314 =
            let uu____67319 =
              let uu____67320 =
                let uu____67329 =
                  let uu____67330 = e_term_aq aq  in embed uu____67330 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____67329  in
              let uu____67333 =
                let uu____67344 =
                  let uu____67353 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____67353  in
                let uu____67354 =
                  let uu____67365 =
                    let uu____67374 =
                      let uu____67375 =
                        let uu____67380 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____67380  in
                      embed uu____67375 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____67374  in
                  [uu____67365]  in
                uu____67344 :: uu____67354  in
              uu____67320 :: uu____67333  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____67319
             in
          uu____67314 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_67419 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_67419.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_67419.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____67437 = FStar_Syntax_Util.head_and_args t  in
      match uu____67437 with
      | (hd1,args) ->
          let uu____67482 =
            let uu____67495 =
              let uu____67496 = FStar_Syntax_Util.un_uinst hd1  in
              uu____67496.FStar_Syntax_Syntax.n  in
            (uu____67495, args)  in
          (match uu____67482 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67511)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____67536 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67536
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67543  -> FStar_Pervasives_Native.Some _67543)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____67546)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____67571 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67571
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _67578  -> FStar_Pervasives_Native.Some _67578)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____67581)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____67606 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____67606
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _67613  -> FStar_Pervasives_Native.Some _67613)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____67616)::(r,uu____67618)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____67653 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____67653
                 (fun l1  ->
                    let uu____67659 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____67659
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _67666  ->
                              FStar_Pervasives_Native.Some _67666)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67669)::(t1,uu____67671)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____67706 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67706
                 (fun b1  ->
                    let uu____67712 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67712
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67719  ->
                              FStar_Pervasives_Native.Some _67719)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67722)::(t1,uu____67724)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____67759 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____67759
                 (fun b1  ->
                    let uu____67765 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____67765
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _67772  ->
                              FStar_Pervasives_Native.Some _67772)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____67775)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____67800 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____67800
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _67807  -> FStar_Pervasives_Native.Some _67807)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____67810)::(t1,uu____67812)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____67847 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____67847
                 (fun b1  ->
                    let uu____67853 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____67853
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _67860  ->
                              FStar_Pervasives_Native.Some _67860)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____67863)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____67888 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____67888
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _67895  -> FStar_Pervasives_Native.Some _67895)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____67898)::(l,uu____67900)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____67935 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____67935
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _67944  -> FStar_Pervasives_Native.Some _67944)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____67947)::(b,uu____67949)::(t1,uu____67951)::
              (t2,uu____67953)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____68008 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____68008
                 (fun r1  ->
                    let uu____68018 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____68018
                      (fun b1  ->
                         let uu____68024 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____68024
                           (fun t11  ->
                              let uu____68030 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____68030
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _68037  ->
                                        FStar_Pervasives_Native.Some _68037)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____68041)::(brs,uu____68043)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____68078 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____68078
                 (fun t2  ->
                    let uu____68084 =
                      let uu____68089 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____68089 brs  in
                    FStar_Util.bind_opt uu____68084
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _68104  ->
                              FStar_Pervasives_Native.Some _68104)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68109)::(t1,uu____68111)::(tacopt,uu____68113)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____68158 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68158
                 (fun e1  ->
                    let uu____68164 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____68164
                      (fun t2  ->
                         let uu____68170 =
                           let uu____68175 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68175 tacopt  in
                         FStar_Util.bind_opt uu____68170
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68190  ->
                                   FStar_Pervasives_Native.Some _68190)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____68195)::(c,uu____68197)::(tacopt,uu____68199)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____68244 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____68244
                 (fun e1  ->
                    let uu____68250 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____68250
                      (fun c1  ->
                         let uu____68256 =
                           let uu____68261 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____68261 tacopt  in
                         FStar_Util.bind_opt uu____68256
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _68276  ->
                                   FStar_Pervasives_Native.Some _68276)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _68296  -> FStar_Pervasives_Native.Some _68296)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____68297 ->
               (if w
                then
                  (let uu____68312 =
                     let uu____68318 =
                       let uu____68320 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____68320
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____68318)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____68312)
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
    let uu____68349 =
      let uu____68354 =
        let uu____68355 =
          let uu____68364 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____68364  in
        let uu____68366 =
          let uu____68377 =
            let uu____68386 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____68386  in
          let uu____68387 =
            let uu____68398 =
              let uu____68407 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____68407  in
            [uu____68398]  in
          uu____68377 :: uu____68387  in
        uu____68355 :: uu____68366  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____68354
       in
    uu____68349 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68460 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68460 with
    | (hd1,args) ->
        let uu____68505 =
          let uu____68518 =
            let uu____68519 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68519.FStar_Syntax_Syntax.n  in
          (uu____68518, args)  in
        (match uu____68505 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____68534)::(idx,uu____68536)::(s,uu____68538)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____68583 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____68583
               (fun nm1  ->
                  let uu____68593 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____68593
                    (fun idx1  ->
                       let uu____68599 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____68599
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _68606  ->
                                 FStar_Pervasives_Native.Some _68606)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____68607 ->
             (if w
              then
                (let uu____68622 =
                   let uu____68628 =
                     let uu____68630 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____68630
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____68628)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____68622)
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
        let uu____68656 =
          let uu____68661 =
            let uu____68662 =
              let uu____68671 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____68671  in
            let uu____68672 =
              let uu____68683 =
                let uu____68692 =
                  let uu____68693 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____68693 rng md  in
                FStar_Syntax_Syntax.as_arg uu____68692  in
              [uu____68683]  in
            uu____68662 :: uu____68672  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____68661
           in
        uu____68656 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____68731 =
          let uu____68736 =
            let uu____68737 =
              let uu____68746 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____68746  in
            let uu____68747 =
              let uu____68758 =
                let uu____68767 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____68767  in
              [uu____68758]  in
            uu____68737 :: uu____68747  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____68736
           in
        uu____68731 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_68794 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_68794.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_68794.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____68813 = FStar_Syntax_Util.head_and_args t1  in
    match uu____68813 with
    | (hd1,args) ->
        let uu____68858 =
          let uu____68871 =
            let uu____68872 = FStar_Syntax_Util.un_uinst hd1  in
            uu____68872.FStar_Syntax_Syntax.n  in
          (uu____68871, args)  in
        (match uu____68858 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____68887)::(md,uu____68889)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____68924 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____68924
               (fun t3  ->
                  let uu____68930 =
                    let uu____68935 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____68935 md  in
                  FStar_Util.bind_opt uu____68930
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _68950  -> FStar_Pervasives_Native.Some _68950)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____68955)::(post,uu____68957)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____68992 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____68992
               (fun pre1  ->
                  let uu____68998 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____68998
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _69005  -> FStar_Pervasives_Native.Some _69005)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _69023  -> FStar_Pervasives_Native.Some _69023)
               FStar_Reflection_Data.C_Unknown
         | uu____69024 ->
             (if w
              then
                (let uu____69039 =
                   let uu____69045 =
                     let uu____69047 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____69047
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69045)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69039)
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
    let uu___1175_69072 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_69072.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_69072.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69093 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69093 with
    | (hd1,args) ->
        let uu____69138 =
          let uu____69153 =
            let uu____69154 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69154.FStar_Syntax_Syntax.n  in
          (uu____69153, args)  in
        (match uu____69138 with
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
         | uu____69226 ->
             (if w
              then
                (let uu____69243 =
                   let uu____69249 =
                     let uu____69251 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____69251
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____69249)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____69243)
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
    let uu____69288 =
      let uu____69289 = FStar_Syntax_Subst.compress t  in
      uu____69289.FStar_Syntax_Syntax.n  in
    match uu____69288 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____69295;
          FStar_Syntax_Syntax.rng = uu____69296;_}
        ->
        let uu____69299 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____69299
    | uu____69300 ->
        (if w
         then
           (let uu____69303 =
              let uu____69309 =
                let uu____69311 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____69311
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____69309)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69303)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____69371 uu____69372 =
    let uu____69394 =
      let uu____69400 = FStar_Ident.range_of_id i  in
      let uu____69401 = FStar_Ident.text_of_id i  in
      (uu____69400, uu____69401)  in
    embed repr rng uu____69394  in
  let unembed_ident t w uu____69429 =
    let uu____69435 = unembed' w repr t  in
    match uu____69435 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____69459 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____69459
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____69466 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____69466
  
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
        let uu____69505 =
          let uu____69510 =
            let uu____69511 =
              let uu____69520 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____69520  in
            let uu____69522 =
              let uu____69533 =
                let uu____69542 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____69542  in
              let uu____69543 =
                let uu____69554 =
                  let uu____69563 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____69563  in
                let uu____69566 =
                  let uu____69577 =
                    let uu____69586 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____69586  in
                  let uu____69587 =
                    let uu____69598 =
                      let uu____69607 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____69607  in
                    [uu____69598]  in
                  uu____69577 :: uu____69587  in
                uu____69554 :: uu____69566  in
              uu____69533 :: uu____69543  in
            uu____69511 :: uu____69522  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____69510
           in
        uu____69505 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____69660 =
          let uu____69665 =
            let uu____69666 =
              let uu____69675 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69675  in
            let uu____69679 =
              let uu____69690 =
                let uu____69699 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____69699  in
              [uu____69690]  in
            uu____69666 :: uu____69679  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____69665
           in
        uu____69660 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____69743 =
          let uu____69748 =
            let uu____69749 =
              let uu____69758 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____69758  in
            let uu____69762 =
              let uu____69773 =
                let uu____69782 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____69782  in
              let uu____69785 =
                let uu____69796 =
                  let uu____69805 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____69805  in
                let uu____69806 =
                  let uu____69817 =
                    let uu____69826 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____69826  in
                  let uu____69827 =
                    let uu____69838 =
                      let uu____69847 =
                        let uu____69848 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____69848 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____69847  in
                    [uu____69838]  in
                  uu____69817 :: uu____69827  in
                uu____69796 :: uu____69806  in
              uu____69773 :: uu____69785  in
            uu____69749 :: uu____69762  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____69748
           in
        uu____69743 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_69914 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_69914.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_69914.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____69933 = FStar_Syntax_Util.head_and_args t1  in
    match uu____69933 with
    | (hd1,args) ->
        let uu____69978 =
          let uu____69991 =
            let uu____69992 = FStar_Syntax_Util.un_uinst hd1  in
            uu____69992.FStar_Syntax_Syntax.n  in
          (uu____69991, args)  in
        (match uu____69978 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____70007)::(us,uu____70009)::(bs,uu____70011)::
            (t2,uu____70013)::(dcs,uu____70015)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____70080 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____70080
               (fun nm1  ->
                  let uu____70098 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____70098
                    (fun us1  ->
                       let uu____70112 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____70112
                         (fun bs1  ->
                            let uu____70118 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____70118
                              (fun t3  ->
                                 let uu____70124 =
                                   let uu____70132 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____70132 dcs  in
                                 FStar_Util.bind_opt uu____70124
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _70162  ->
                                           FStar_Pervasives_Native.Some
                                             _70162)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____70171)::(fvar1,uu____70173)::(univs1,uu____70175)::
            (ty,uu____70177)::(t2,uu____70179)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____70244 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____70244
               (fun r1  ->
                  let uu____70254 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____70254
                    (fun fvar2  ->
                       let uu____70260 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____70260
                         (fun univs2  ->
                            let uu____70274 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____70274
                              (fun ty1  ->
                                 let uu____70280 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____70280
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _70287  ->
                                           FStar_Pervasives_Native.Some
                                             _70287)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____70306 ->
             (if w
              then
                (let uu____70321 =
                   let uu____70327 =
                     let uu____70329 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____70329
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70327)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70321)
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
          let uu____70355 =
            let uu____70360 =
              let uu____70361 =
                let uu____70370 =
                  let uu____70371 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____70371  in
                FStar_Syntax_Syntax.as_arg uu____70370  in
              [uu____70361]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____70360
             in
          uu____70355 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____70393 =
            let uu____70398 =
              let uu____70399 =
                let uu____70408 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____70408  in
              let uu____70409 =
                let uu____70420 =
                  let uu____70429 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____70429  in
                [uu____70420]  in
              uu____70399 :: uu____70409  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____70398
             in
          uu____70393 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_70456 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_70456.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_70456.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____70477 = FStar_Syntax_Util.head_and_args t1  in
    match uu____70477 with
    | (hd1,args) ->
        let uu____70522 =
          let uu____70535 =
            let uu____70536 = FStar_Syntax_Util.un_uinst hd1  in
            uu____70536.FStar_Syntax_Syntax.n  in
          (uu____70535, args)  in
        (match uu____70522 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____70566)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____70591 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____70591
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _70598  -> FStar_Pervasives_Native.Some _70598)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____70601)::(e2,uu____70603)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____70638 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____70638
               (fun e11  ->
                  let uu____70644 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____70644
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _70651  -> FStar_Pervasives_Native.Some _70651)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____70652 ->
             (if w
              then
                (let uu____70667 =
                   let uu____70673 =
                     let uu____70675 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____70675
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____70673)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____70667)
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
    let uu____70699 =
      let uu____70704 =
        let uu____70705 =
          let uu____70714 =
            let uu____70715 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____70715  in
          FStar_Syntax_Syntax.as_arg uu____70714  in
        [uu____70705]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____70704
       in
    uu____70699 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70741 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____70741 with
    | (bv,aq) ->
        let uu____70748 =
          let uu____70753 =
            let uu____70754 =
              let uu____70763 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____70763  in
            let uu____70764 =
              let uu____70775 =
                let uu____70784 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____70784  in
              [uu____70775]  in
            uu____70754 :: uu____70764  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____70753
           in
        uu____70748 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70818 =
      let uu____70823 =
        let uu____70824 =
          let uu____70833 =
            let uu____70834 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____70841 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____70834 i.FStar_Syntax_Syntax.rng uu____70841  in
          FStar_Syntax_Syntax.as_arg uu____70833  in
        [uu____70824]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____70823
       in
    uu____70818 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70873 =
      let uu____70878 =
        let uu____70879 =
          let uu____70888 =
            let uu____70889 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____70889  in
          FStar_Syntax_Syntax.as_arg uu____70888  in
        [uu____70879]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____70878
       in
    uu____70873 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____70921 =
      let uu____70926 =
        let uu____70927 =
          let uu____70936 =
            let uu____70937 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____70937  in
          FStar_Syntax_Syntax.as_arg uu____70936  in
        [uu____70927]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____70926
       in
    uu____70921 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  