open Prims
let mk_emb :
  'Auu____59386 .
    (FStar_Range.range -> 'Auu____59386 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____59386 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____59386 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____59430 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____59430
  
let embed :
  'Auu____59457 .
    'Auu____59457 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____59457 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____59477 = FStar_Syntax_Embeddings.embed e x  in
        uu____59477 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____59495 .
    Prims.bool ->
      'Auu____59495 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____59495 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____59519 = FStar_Syntax_Embeddings.unembed e x  in
        uu____59519 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____59557 =
      let uu____59558 = FStar_Syntax_Subst.compress t  in
      uu____59558.FStar_Syntax_Syntax.n  in
    match uu____59557 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____59564;
          FStar_Syntax_Syntax.rng = uu____59565;_}
        ->
        let uu____59568 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59568
    | uu____59569 ->
        (if w
         then
           (let uu____59572 =
              let uu____59578 =
                let uu____59580 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____59580  in
              (FStar_Errors.Warning_NotEmbedded, uu____59578)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59572)
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
    let uu____59617 =
      let uu____59618 = FStar_Syntax_Subst.compress t  in
      uu____59618.FStar_Syntax_Syntax.n  in
    match uu____59617 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____59624;
          FStar_Syntax_Syntax.rng = uu____59625;_}
        ->
        let uu____59628 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59628
    | uu____59629 ->
        (if w
         then
           (let uu____59632 =
              let uu____59638 =
                let uu____59640 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____59640
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____59638)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59632)
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
          let uu____59692 = f x  in
          FStar_Util.bind_opt uu____59692
            (fun x1  ->
               let uu____59700 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59700
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
        let uu____59769 =
          mapM_opt
            (fun uu____59782  ->
               match uu____59782 with
               | (bv,e) ->
                   let uu____59791 = unembed_term w e  in
                   FStar_Util.bind_opt uu____59791
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____59769
          (fun s  ->
             let uu____59805 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____59805)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____59807 =
        let uu____59808 = FStar_Syntax_Subst.compress t1  in
        uu____59808.FStar_Syntax_Syntax.n  in
      match uu____59807 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____59819 ->
          (if w
           then
             (let uu____59822 =
                let uu____59828 =
                  let uu____59830 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____59830
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____59828)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____59822)
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
          let uu____59865 =
            let uu____59870 =
              let uu____59871 =
                let uu____59880 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____59880  in
              [uu____59871]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____59870
             in
          uu____59865 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_59897 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_59897.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_59897.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____59918 = FStar_Syntax_Util.head_and_args t1  in
    match uu____59918 with
    | (hd1,args) ->
        let uu____59963 =
          let uu____59978 =
            let uu____59979 = FStar_Syntax_Util.un_uinst hd1  in
            uu____59979.FStar_Syntax_Syntax.n  in
          (uu____59978, args)  in
        (match uu____59963 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____60034)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____60069 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____60069
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____60074 ->
             (if w
              then
                (let uu____60091 =
                   let uu____60097 =
                     let uu____60099 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____60099
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60097)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60091)
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
    let uu____60139 =
      let uu____60140 = FStar_Syntax_Subst.compress t  in
      uu____60140.FStar_Syntax_Syntax.n  in
    match uu____60139 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____60146;
          FStar_Syntax_Syntax.rng = uu____60147;_}
        ->
        let uu____60150 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60150
    | uu____60151 ->
        (if w
         then
           (let uu____60154 =
              let uu____60160 =
                let uu____60162 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____60162  in
              (FStar_Errors.Warning_NotEmbedded, uu____60160)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60154)
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
    let uu____60199 =
      let uu____60200 = FStar_Syntax_Subst.compress t  in
      uu____60200.FStar_Syntax_Syntax.n  in
    match uu____60199 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____60206;
          FStar_Syntax_Syntax.rng = uu____60207;_}
        ->
        let uu____60210 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60210
    | uu____60211 ->
        (if w
         then
           (let uu____60214 =
              let uu____60220 =
                let uu____60222 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____60222  in
              (FStar_Errors.Warning_NotEmbedded, uu____60220)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60214)
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
    let uu____60259 =
      let uu____60260 = FStar_Syntax_Subst.compress t  in
      uu____60260.FStar_Syntax_Syntax.n  in
    match uu____60259 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____60266;
          FStar_Syntax_Syntax.rng = uu____60267;_}
        ->
        let uu____60270 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60270
    | uu____60271 ->
        (if w
         then
           (let uu____60274 =
              let uu____60280 =
                let uu____60282 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____60282  in
              (FStar_Errors.Warning_NotEmbedded, uu____60280)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60274)
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
          let uu____60308 =
            let uu____60313 =
              let uu____60314 =
                let uu____60323 =
                  let uu____60324 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____60324  in
                FStar_Syntax_Syntax.as_arg uu____60323  in
              [uu____60314]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____60313
             in
          uu____60308 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____60344 =
            let uu____60349 =
              let uu____60350 =
                let uu____60359 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____60359  in
              [uu____60350]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____60349
             in
          uu____60344 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____60378 =
            let uu____60383 =
              let uu____60384 =
                let uu____60393 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____60393  in
              [uu____60384]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____60383
             in
          uu____60378 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____60411 =
            let uu____60416 =
              let uu____60417 =
                let uu____60426 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____60426  in
              [uu____60417]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____60416
             in
          uu____60411 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_60446 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_60446.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_60446.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____60467 = FStar_Syntax_Util.head_and_args t1  in
    match uu____60467 with
    | (hd1,args) ->
        let uu____60512 =
          let uu____60527 =
            let uu____60528 = FStar_Syntax_Util.un_uinst hd1  in
            uu____60528.FStar_Syntax_Syntax.n  in
          (uu____60527, args)  in
        (match uu____60512 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____60602)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____60637 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____60637
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _60644  -> FStar_Pervasives_Native.Some _60644)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____60647)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____60682 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____60682
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _60693  -> FStar_Pervasives_Native.Some _60693)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____60696)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____60731 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____60731
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _60738  -> FStar_Pervasives_Native.Some _60738)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _60760  -> FStar_Pervasives_Native.Some _60760)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____60763)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____60798 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____60798
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _60817  -> FStar_Pervasives_Native.Some _60817)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____60818 ->
             (if w
              then
                (let uu____60835 =
                   let uu____60841 =
                     let uu____60843 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____60843
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60841)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60835)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____60856  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60869 =
            let uu____60874 =
              let uu____60875 =
                let uu____60884 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____60884  in
              [uu____60875]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____60874
             in
          uu____60869 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60907 =
            let uu____60912 =
              let uu____60913 =
                let uu____60922 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____60922  in
              let uu____60923 =
                let uu____60934 =
                  let uu____60943 =
                    let uu____60944 =
                      let uu____60949 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____60949  in
                    embed uu____60944 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____60943  in
                [uu____60934]  in
              uu____60913 :: uu____60923  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____60912
             in
          uu____60907 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60979 =
            let uu____60984 =
              let uu____60985 =
                let uu____60994 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____60994  in
              [uu____60985]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____60984
             in
          uu____60979 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____61012 =
            let uu____61017 =
              let uu____61018 =
                let uu____61027 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61027  in
              [uu____61018]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____61017
             in
          uu____61012 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____61046 =
            let uu____61051 =
              let uu____61052 =
                let uu____61061 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61061  in
              let uu____61062 =
                let uu____61073 =
                  let uu____61082 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____61082  in
                [uu____61073]  in
              uu____61052 :: uu____61062  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____61051
             in
          uu____61046 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____61125 = FStar_Syntax_Util.head_and_args t1  in
      match uu____61125 with
      | (hd1,args) ->
          let uu____61170 =
            let uu____61183 =
              let uu____61184 = FStar_Syntax_Util.un_uinst hd1  in
              uu____61184.FStar_Syntax_Syntax.n  in
            (uu____61183, args)  in
          (match uu____61170 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____61199)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____61224 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____61224
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _61231  -> FStar_Pervasives_Native.Some _61231)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____61234)::(ps,uu____61236)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____61271 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____61271
                 (fun f1  ->
                    let uu____61277 =
                      let uu____61282 =
                        let uu____61287 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____61287  in
                      unembed' w uu____61282 ps  in
                    FStar_Util.bind_opt uu____61277
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _61300  ->
                              FStar_Pervasives_Native.Some _61300)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61305)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____61330 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61330
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61337  -> FStar_Pervasives_Native.Some _61337)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61340)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____61365 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61365
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61372  -> FStar_Pervasives_Native.Some _61372)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____61375)::(t2,uu____61377)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____61412 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61412
                 (fun bv1  ->
                    let uu____61418 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____61418
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _61425  ->
                              FStar_Pervasives_Native.Some _61425)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____61426 ->
               (if w
                then
                  (let uu____61441 =
                     let uu____61447 =
                       let uu____61449 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____61449
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____61447)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____61441)
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
    let uu____61476 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____61476
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____61491 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____61491 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61514 =
            let uu____61519 =
              let uu____61520 =
                let uu____61529 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61529  in
              [uu____61520]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____61519
             in
          uu____61514 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____61547 =
            let uu____61552 =
              let uu____61553 =
                let uu____61562 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61562  in
              [uu____61553]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____61552
             in
          uu____61547 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61580 =
            let uu____61585 =
              let uu____61586 =
                let uu____61595 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61595  in
              [uu____61586]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____61585
             in
          uu____61580 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61614 =
            let uu____61619 =
              let uu____61620 =
                let uu____61629 =
                  let uu____61630 = e_term_aq aq  in
                  embed uu____61630 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____61629  in
              let uu____61633 =
                let uu____61644 =
                  let uu____61653 =
                    let uu____61654 = e_argv_aq aq  in
                    embed uu____61654 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____61653  in
                [uu____61644]  in
              uu____61620 :: uu____61633  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____61619
             in
          uu____61614 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____61691 =
            let uu____61696 =
              let uu____61697 =
                let uu____61706 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61706  in
              let uu____61707 =
                let uu____61718 =
                  let uu____61727 =
                    let uu____61728 = e_term_aq aq  in
                    embed uu____61728 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61727  in
                [uu____61718]  in
              uu____61697 :: uu____61707  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____61696
             in
          uu____61691 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61757 =
            let uu____61762 =
              let uu____61763 =
                let uu____61772 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61772  in
              let uu____61773 =
                let uu____61784 =
                  let uu____61793 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____61793  in
                [uu____61784]  in
              uu____61763 :: uu____61773  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____61762
             in
          uu____61757 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61819 =
            let uu____61824 =
              let uu____61825 =
                let uu____61834 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____61834  in
              [uu____61825]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____61824
             in
          uu____61819 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____61853 =
            let uu____61858 =
              let uu____61859 =
                let uu____61868 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61868  in
              let uu____61869 =
                let uu____61880 =
                  let uu____61889 =
                    let uu____61890 = e_term_aq aq  in
                    embed uu____61890 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61889  in
                [uu____61880]  in
              uu____61859 :: uu____61869  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____61858
             in
          uu____61853 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61918 =
            let uu____61923 =
              let uu____61924 =
                let uu____61933 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____61933  in
              [uu____61924]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____61923
             in
          uu____61918 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61952 =
            let uu____61957 =
              let uu____61958 =
                let uu____61967 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____61967  in
              let uu____61968 =
                let uu____61979 =
                  let uu____61988 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____61988  in
                [uu____61979]  in
              uu____61958 :: uu____61968  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____61957
             in
          uu____61952 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____62023 =
            let uu____62028 =
              let uu____62029 =
                let uu____62038 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____62038  in
              let uu____62040 =
                let uu____62051 =
                  let uu____62060 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____62060  in
                let uu____62061 =
                  let uu____62072 =
                    let uu____62081 =
                      let uu____62082 = e_term_aq aq  in
                      embed uu____62082 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____62081  in
                  let uu____62085 =
                    let uu____62096 =
                      let uu____62105 =
                        let uu____62106 = e_term_aq aq  in
                        embed uu____62106 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____62105  in
                    [uu____62096]  in
                  uu____62072 :: uu____62085  in
                uu____62051 :: uu____62061  in
              uu____62029 :: uu____62040  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____62028
             in
          uu____62023 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____62155 =
            let uu____62160 =
              let uu____62161 =
                let uu____62170 =
                  let uu____62171 = e_term_aq aq  in embed uu____62171 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____62170  in
              let uu____62174 =
                let uu____62185 =
                  let uu____62194 =
                    let uu____62195 =
                      let uu____62204 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____62204  in
                    embed uu____62195 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____62194  in
                [uu____62185]  in
              uu____62161 :: uu____62174  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____62160
             in
          uu____62155 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____62252 =
            let uu____62257 =
              let uu____62258 =
                let uu____62267 =
                  let uu____62268 = e_term_aq aq  in embed uu____62268 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62267  in
              let uu____62271 =
                let uu____62282 =
                  let uu____62291 =
                    let uu____62292 = e_term_aq aq  in
                    embed uu____62292 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____62291  in
                let uu____62295 =
                  let uu____62306 =
                    let uu____62315 =
                      let uu____62316 =
                        let uu____62321 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62321  in
                      embed uu____62316 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62315  in
                  [uu____62306]  in
                uu____62282 :: uu____62295  in
              uu____62258 :: uu____62271  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____62257
             in
          uu____62252 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____62365 =
            let uu____62370 =
              let uu____62371 =
                let uu____62380 =
                  let uu____62381 = e_term_aq aq  in embed uu____62381 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62380  in
              let uu____62384 =
                let uu____62395 =
                  let uu____62404 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____62404  in
                let uu____62405 =
                  let uu____62416 =
                    let uu____62425 =
                      let uu____62426 =
                        let uu____62431 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62431  in
                      embed uu____62426 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62425  in
                  [uu____62416]  in
                uu____62395 :: uu____62405  in
              uu____62371 :: uu____62384  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____62370
             in
          uu____62365 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_62468 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_62468.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_62468.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____62486 = FStar_Syntax_Util.head_and_args t  in
      match uu____62486 with
      | (hd1,args) ->
          let uu____62531 =
            let uu____62544 =
              let uu____62545 = FStar_Syntax_Util.un_uinst hd1  in
              uu____62545.FStar_Syntax_Syntax.n  in
            (uu____62544, args)  in
          (match uu____62531 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62560)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____62585 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62585
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62592  -> FStar_Pervasives_Native.Some _62592)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62595)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____62620 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62620
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62627  -> FStar_Pervasives_Native.Some _62627)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____62630)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____62655 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____62655
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _62662  -> FStar_Pervasives_Native.Some _62662)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____62665)::(r,uu____62667)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____62702 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____62702
                 (fun l1  ->
                    let uu____62708 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____62708
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _62715  ->
                              FStar_Pervasives_Native.Some _62715)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62718)::(t1,uu____62720)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____62755 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62755
                 (fun b1  ->
                    let uu____62761 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62761
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62768  ->
                              FStar_Pervasives_Native.Some _62768)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62771)::(t1,uu____62773)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____62808 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62808
                 (fun b1  ->
                    let uu____62814 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____62814
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _62821  ->
                              FStar_Pervasives_Native.Some _62821)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____62824)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____62849 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____62849
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _62856  -> FStar_Pervasives_Native.Some _62856)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62859)::(t1,uu____62861)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____62896 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62896
                 (fun b1  ->
                    let uu____62902 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62902
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62909  ->
                              FStar_Pervasives_Native.Some _62909)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____62912)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____62937 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____62937
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _62944  -> FStar_Pervasives_Native.Some _62944)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____62947)::(l,uu____62949)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____62984 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____62984
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _62993  -> FStar_Pervasives_Native.Some _62993)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____62996)::(b,uu____62998)::(t1,uu____63000)::
              (t2,uu____63002)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____63057 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____63057
                 (fun r1  ->
                    let uu____63067 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____63067
                      (fun b1  ->
                         let uu____63073 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____63073
                           (fun t11  ->
                              let uu____63079 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____63079
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _63086  ->
                                        FStar_Pervasives_Native.Some _63086)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____63090)::(brs,uu____63092)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____63127 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____63127
                 (fun t2  ->
                    let uu____63133 =
                      let uu____63138 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____63138 brs  in
                    FStar_Util.bind_opt uu____63133
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _63153  ->
                              FStar_Pervasives_Native.Some _63153)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63158)::(t1,uu____63160)::(tacopt,uu____63162)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____63207 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63207
                 (fun e1  ->
                    let uu____63213 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____63213
                      (fun t2  ->
                         let uu____63219 =
                           let uu____63224 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63224 tacopt  in
                         FStar_Util.bind_opt uu____63219
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63239  ->
                                   FStar_Pervasives_Native.Some _63239)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63244)::(c,uu____63246)::(tacopt,uu____63248)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____63293 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63293
                 (fun e1  ->
                    let uu____63299 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____63299
                      (fun c1  ->
                         let uu____63305 =
                           let uu____63310 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63310 tacopt  in
                         FStar_Util.bind_opt uu____63305
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63325  ->
                                   FStar_Pervasives_Native.Some _63325)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _63345  -> FStar_Pervasives_Native.Some _63345)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____63346 ->
               (if w
                then
                  (let uu____63361 =
                     let uu____63367 =
                       let uu____63369 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____63369
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____63367)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____63361)
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
    let uu____63398 =
      let uu____63403 =
        let uu____63404 =
          let uu____63413 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____63413  in
        let uu____63415 =
          let uu____63426 =
            let uu____63435 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____63435  in
          let uu____63436 =
            let uu____63447 =
              let uu____63456 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____63456  in
            [uu____63447]  in
          uu____63426 :: uu____63436  in
        uu____63404 :: uu____63415  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____63403
       in
    uu____63398 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63507 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63507 with
    | (hd1,args) ->
        let uu____63552 =
          let uu____63565 =
            let uu____63566 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63566.FStar_Syntax_Syntax.n  in
          (uu____63565, args)  in
        (match uu____63552 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____63581)::(idx,uu____63583)::(s,uu____63585)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____63630 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____63630
               (fun nm1  ->
                  let uu____63640 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____63640
                    (fun idx1  ->
                       let uu____63646 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____63646
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _63653  ->
                                 FStar_Pervasives_Native.Some _63653)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____63654 ->
             (if w
              then
                (let uu____63669 =
                   let uu____63675 =
                     let uu____63677 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____63677
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____63675)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____63669)
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
        let uu____63703 =
          let uu____63708 =
            let uu____63709 =
              let uu____63718 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____63718  in
            let uu____63719 =
              let uu____63730 =
                let uu____63739 =
                  let uu____63740 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____63740 rng md  in
                FStar_Syntax_Syntax.as_arg uu____63739  in
              [uu____63730]  in
            uu____63709 :: uu____63719  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____63708
           in
        uu____63703 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____63776 =
          let uu____63781 =
            let uu____63782 =
              let uu____63791 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____63791  in
            let uu____63792 =
              let uu____63803 =
                let uu____63812 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____63812  in
              [uu____63803]  in
            uu____63782 :: uu____63792  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____63781
           in
        uu____63776 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_63837 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_63837.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_63837.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63856 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63856 with
    | (hd1,args) ->
        let uu____63901 =
          let uu____63914 =
            let uu____63915 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63915.FStar_Syntax_Syntax.n  in
          (uu____63914, args)  in
        (match uu____63901 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____63930)::(md,uu____63932)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____63967 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____63967
               (fun t3  ->
                  let uu____63973 =
                    let uu____63978 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____63978 md  in
                  FStar_Util.bind_opt uu____63973
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _63993  -> FStar_Pervasives_Native.Some _63993)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____63998)::(post,uu____64000)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____64035 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____64035
               (fun pre1  ->
                  let uu____64041 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____64041
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _64048  -> FStar_Pervasives_Native.Some _64048)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _64066  -> FStar_Pervasives_Native.Some _64066)
               FStar_Reflection_Data.C_Unknown
         | uu____64067 ->
             (if w
              then
                (let uu____64082 =
                   let uu____64088 =
                     let uu____64090 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____64090
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64088)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64082)
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
    let uu___1175_64115 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_64115.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_64115.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64136 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64136 with
    | (hd1,args) ->
        let uu____64181 =
          let uu____64196 =
            let uu____64197 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64197.FStar_Syntax_Syntax.n  in
          (uu____64196, args)  in
        (match uu____64181 with
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
         | uu____64269 ->
             (if w
              then
                (let uu____64286 =
                   let uu____64292 =
                     let uu____64294 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____64294
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64292)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64286)
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
    let uu____64331 =
      let uu____64332 = FStar_Syntax_Subst.compress t  in
      uu____64332.FStar_Syntax_Syntax.n  in
    match uu____64331 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____64338;
          FStar_Syntax_Syntax.rng = uu____64339;_}
        ->
        let uu____64342 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64342
    | uu____64343 ->
        (if w
         then
           (let uu____64346 =
              let uu____64352 =
                let uu____64354 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____64354
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64352)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64346)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____64394 uu____64395 =
    let uu____64397 =
      let uu____64403 = FStar_Ident.range_of_id i  in
      let uu____64404 = FStar_Ident.text_of_id i  in
      (uu____64403, uu____64404)  in
    embed repr rng uu____64397  in
  let unembed_ident t w uu____64431 =
    let uu____64436 = unembed' w repr t  in
    match uu____64436 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____64460 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____64460
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____64467 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____64467
  
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
        let uu____64506 =
          let uu____64511 =
            let uu____64512 =
              let uu____64521 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____64521  in
            let uu____64523 =
              let uu____64534 =
                let uu____64543 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____64543  in
              let uu____64544 =
                let uu____64555 =
                  let uu____64564 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____64564  in
                let uu____64567 =
                  let uu____64578 =
                    let uu____64587 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____64587  in
                  let uu____64588 =
                    let uu____64599 =
                      let uu____64608 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____64608  in
                    [uu____64599]  in
                  uu____64578 :: uu____64588  in
                uu____64555 :: uu____64567  in
              uu____64534 :: uu____64544  in
            uu____64512 :: uu____64523  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____64511
           in
        uu____64506 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____64659 =
          let uu____64664 =
            let uu____64665 =
              let uu____64674 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64674  in
            let uu____64678 =
              let uu____64689 =
                let uu____64698 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____64698  in
              [uu____64689]  in
            uu____64665 :: uu____64678  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____64664
           in
        uu____64659 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____64740 =
          let uu____64745 =
            let uu____64746 =
              let uu____64755 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64755  in
            let uu____64759 =
              let uu____64770 =
                let uu____64779 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____64779  in
              let uu____64782 =
                let uu____64793 =
                  let uu____64802 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____64802  in
                let uu____64803 =
                  let uu____64814 =
                    let uu____64823 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____64823  in
                  let uu____64824 =
                    let uu____64835 =
                      let uu____64844 =
                        let uu____64845 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____64845 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____64844  in
                    [uu____64835]  in
                  uu____64814 :: uu____64824  in
                uu____64793 :: uu____64803  in
              uu____64770 :: uu____64782  in
            uu____64746 :: uu____64759  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____64745
           in
        uu____64740 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_64909 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_64909.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_64909.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64928 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64928 with
    | (hd1,args) ->
        let uu____64973 =
          let uu____64986 =
            let uu____64987 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64987.FStar_Syntax_Syntax.n  in
          (uu____64986, args)  in
        (match uu____64973 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____65002)::(us,uu____65004)::(bs,uu____65006)::
            (t2,uu____65008)::(dcs,uu____65010)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____65075 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____65075
               (fun nm1  ->
                  let uu____65093 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____65093
                    (fun us1  ->
                       let uu____65107 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____65107
                         (fun bs1  ->
                            let uu____65113 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____65113
                              (fun t3  ->
                                 let uu____65119 =
                                   let uu____65127 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____65127 dcs  in
                                 FStar_Util.bind_opt uu____65119
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _65157  ->
                                           FStar_Pervasives_Native.Some
                                             _65157)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____65166)::(fvar1,uu____65168)::(univs1,uu____65170)::
            (ty,uu____65172)::(t2,uu____65174)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____65239 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____65239
               (fun r1  ->
                  let uu____65249 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____65249
                    (fun fvar2  ->
                       let uu____65255 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____65255
                         (fun univs2  ->
                            let uu____65269 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____65269
                              (fun ty1  ->
                                 let uu____65275 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____65275
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _65282  ->
                                           FStar_Pervasives_Native.Some
                                             _65282)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____65301 ->
             (if w
              then
                (let uu____65316 =
                   let uu____65322 =
                     let uu____65324 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____65324
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65322)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65316)
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
          let uu____65350 =
            let uu____65355 =
              let uu____65356 =
                let uu____65365 =
                  let uu____65366 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65366  in
                FStar_Syntax_Syntax.as_arg uu____65365  in
              [uu____65356]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____65355
             in
          uu____65350 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____65386 =
            let uu____65391 =
              let uu____65392 =
                let uu____65401 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____65401  in
              let uu____65402 =
                let uu____65413 =
                  let uu____65422 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____65422  in
                [uu____65413]  in
              uu____65392 :: uu____65402  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____65391
             in
          uu____65386 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_65447 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_65447.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_65447.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65468 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65468 with
    | (hd1,args) ->
        let uu____65513 =
          let uu____65526 =
            let uu____65527 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65527.FStar_Syntax_Syntax.n  in
          (uu____65526, args)  in
        (match uu____65513 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65557)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____65582 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65582
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65589  -> FStar_Pervasives_Native.Some _65589)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____65592)::(e2,uu____65594)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____65629 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____65629
               (fun e11  ->
                  let uu____65635 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____65635
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _65642  -> FStar_Pervasives_Native.Some _65642)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____65643 ->
             (if w
              then
                (let uu____65658 =
                   let uu____65664 =
                     let uu____65666 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____65666
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65664)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65658)
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
    let uu____65690 =
      let uu____65695 =
        let uu____65696 =
          let uu____65705 =
            let uu____65706 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____65706  in
          FStar_Syntax_Syntax.as_arg uu____65705  in
        [uu____65696]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____65695
       in
    uu____65690 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65730 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____65730 with
    | (bv,aq) ->
        let uu____65737 =
          let uu____65742 =
            let uu____65743 =
              let uu____65752 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____65752  in
            let uu____65753 =
              let uu____65764 =
                let uu____65773 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____65773  in
              [uu____65764]  in
            uu____65743 :: uu____65753  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____65742
           in
        uu____65737 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65805 =
      let uu____65810 =
        let uu____65811 =
          let uu____65820 =
            let uu____65821 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____65828 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____65821 i.FStar_Syntax_Syntax.rng uu____65828  in
          FStar_Syntax_Syntax.as_arg uu____65820  in
        [uu____65811]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____65810
       in
    uu____65805 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65858 =
      let uu____65863 =
        let uu____65864 =
          let uu____65873 =
            let uu____65874 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____65874  in
          FStar_Syntax_Syntax.as_arg uu____65873  in
        [uu____65864]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____65863
       in
    uu____65858 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65904 =
      let uu____65909 =
        let uu____65910 =
          let uu____65919 =
            let uu____65920 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____65920  in
          FStar_Syntax_Syntax.as_arg uu____65919  in
        [uu____65910]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____65909
       in
    uu____65904 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  