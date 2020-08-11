open Prims
let mk_emb :
  'uuuuuu8 .
    (FStar_Range.range -> 'uuuuuu8 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'uuuuuu8 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'uuuuuu8 FStar_Syntax_Embeddings.embedding
  =
  fun f ->
    fun g ->
      fun t ->
        let uu____50 = FStar_Syntax_Embeddings.term_as_fv t in
        FStar_Syntax_Embeddings.mk_emb
          (fun x -> fun r -> fun _topt -> fun _norm -> f r x)
          (fun x -> fun w -> fun _norm -> g w x) uu____50
let embed :
  'uuuuuu75 .
    'uuuuuu75 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'uuuuuu75 -> FStar_Syntax_Syntax.term
  =
  fun e ->
    fun r ->
      fun x ->
        let uu____95 = FStar_Syntax_Embeddings.embed e x in
        uu____95 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
let unembed' :
  'uuuuuu112 .
    Prims.bool ->
      'uuuuuu112 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term -> 'uuuuuu112 FStar_Pervasives_Native.option
  =
  fun w ->
    fun e ->
      fun x ->
        let uu____134 = FStar_Syntax_Embeddings.unembed e x in
        uu____134 w FStar_Syntax_Embeddings.id_norm_cb
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng) in
  let unembed_bv w t =
    let uu____169 =
      let uu____170 = FStar_Syntax_Subst.compress t in
      uu____170.FStar_Syntax_Syntax.n in
    match uu____169 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv;
          FStar_Syntax_Syntax.ltyp = uu____176;
          FStar_Syntax_Syntax.rng = uu____177;_}
        ->
        let uu____180 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____180
    | uu____181 ->
        (if w
         then
           (let uu____183 =
              let uu____188 =
                let uu____189 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded bv: %s" uu____189 in
              (FStar_Errors.Warning_NotEmbedded, uu____188) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____183)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv
let (e_binder : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding)
  =
  let embed_binder rng b =
    FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng) in
  let unembed_binder w t =
    let uu____219 =
      let uu____220 = FStar_Syntax_Subst.compress t in
      uu____220.FStar_Syntax_Syntax.n in
    match uu____219 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder;
          FStar_Syntax_Syntax.ltyp = uu____226;
          FStar_Syntax_Syntax.rng = uu____227;_}
        ->
        let uu____230 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____230
    | uu____231 ->
        (if w
         then
           (let uu____233 =
              let uu____238 =
                let uu____239 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded binder: %s" uu____239 in
              (FStar_Errors.Warning_NotEmbedded, uu____238) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____233)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_binder unembed_binder FStar_Reflection_Data.fstar_refl_binder
let (e_optionstate :
  FStar_Options.optionstate FStar_Syntax_Embeddings.embedding) =
  let embed_optionstate rng b =
    FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_optionstate
      FStar_Syntax_Syntax.Lazy_optionstate (FStar_Pervasives_Native.Some rng) in
  let unembed_optionstate w t =
    let uu____269 =
      let uu____270 = FStar_Syntax_Subst.compress t in
      uu____270.FStar_Syntax_Syntax.n in
    match uu____269 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_optionstate;
          FStar_Syntax_Syntax.ltyp = uu____276;
          FStar_Syntax_Syntax.rng = uu____277;_}
        ->
        let uu____280 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____280
    | uu____281 ->
        (if w
         then
           (let uu____283 =
              let uu____288 =
                let uu____289 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded optionstate: %s"
                  uu____289 in
              (FStar_Errors.Warning_NotEmbedded, uu____288) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____283)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_optionstate unembed_optionstate
    FStar_Reflection_Data.fstar_refl_optionstate
let (uu___61 : unit) =
  FStar_ST.op_Colon_Equals FStar_Reflection_Basic.e_optionstate_hook
    (FStar_Pervasives_Native.Some e_optionstate)
let rec mapM_opt :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.Some []
      | x::xs ->
          let uu____352 = f x in
          FStar_Util.bind_opt uu____352
            (fun x1 ->
               let uu____360 = mapM_opt f xs in
               FStar_Util.bind_opt uu____360
                 (fun xs1 -> FStar_Pervasives_Native.Some (x1 :: xs1)))
let (e_term_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding)
  =
  fun aq ->
    let embed_term rng t =
      let qi =
        {
          FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
          FStar_Syntax_Syntax.antiquotes = aq
        } in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (t, qi)) rng in
    let rec unembed_term w t =
      let apply_antiquotes t1 aq1 =
        let uu____426 =
          mapM_opt
            (fun uu____439 ->
               match uu____439 with
               | (bv, e) ->
                   let uu____448 = unembed_term w e in
                   FStar_Util.bind_opt uu____448
                     (fun e1 ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1 in
        FStar_Util.bind_opt uu____426
          (fun s ->
             let uu____462 = FStar_Syntax_Subst.subst s t1 in
             FStar_Pervasives_Native.Some uu____462) in
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____464 =
        let uu____465 = FStar_Syntax_Subst.compress t1 in
        uu____465.FStar_Syntax_Syntax.n in
      match uu____464 with
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____476 ->
          (if w
           then
             (let uu____478 =
                let uu____483 =
                  let uu____484 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.format1 "Not an embedded term: %s" uu____484 in
                (FStar_Errors.Warning_NotEmbedded, uu____483) in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____478)
           else ();
           FStar_Pervasives_Native.None) in
    mk_emb embed_term unembed_term FStar_Syntax_Syntax.t_term
let (e_term : FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding) =
  e_term_aq []
let (e_aqualv :
  FStar_Reflection_Data.aqualv FStar_Syntax_Embeddings.embedding) =
  let embed_aqualv rng q =
    let r =
      match q with
      | FStar_Reflection_Data.Q_Explicit ->
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Q_Implicit ->
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Q_Meta t ->
          let uu____513 =
            let uu____514 =
              let uu____523 = embed e_term rng t in
              FStar_Syntax_Syntax.as_arg uu____523 in
            [uu____514] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
            uu____513 FStar_Range.dummyRange in
    let uu___104_540 = r in
    {
      FStar_Syntax_Syntax.n = (uu___104_540.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___104_540.FStar_Syntax_Syntax.vars)
    } in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____559 = FStar_Syntax_Util.head_and_args t1 in
    match uu____559 with
    | (hd, args) ->
        let uu____604 =
          let uu____619 =
            let uu____620 = FStar_Syntax_Util.un_uinst hd in
            uu____620.FStar_Syntax_Syntax.n in
          (uu____619, args) in
        (match uu____604 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv, (t2, uu____675)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____710 = unembed' w e_term t2 in
             FStar_Util.bind_opt uu____710
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____715 ->
             (if w
              then
                (let uu____731 =
                   let uu____736 =
                     let uu____737 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____737 in
                   (FStar_Errors.Warning_NotEmbedded, uu____736) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____731)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_aqualv unembed_aqualv FStar_Reflection_Data.fstar_refl_aqualv
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_list e_binder
let (e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings.embedding) =
  let embed_fv rng fv =
    FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng) in
  let unembed_fv w t =
    let uu____769 =
      let uu____770 = FStar_Syntax_Subst.compress t in
      uu____770.FStar_Syntax_Syntax.n in
    match uu____769 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar;
          FStar_Syntax_Syntax.ltyp = uu____776;
          FStar_Syntax_Syntax.rng = uu____777;_}
        ->
        let uu____780 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____780
    | uu____781 ->
        (if w
         then
           (let uu____783 =
              let uu____788 =
                let uu____789 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____789 in
              (FStar_Errors.Warning_NotEmbedded, uu____788) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____783)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv
let (e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding) =
  let embed_comp rng c =
    FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng) in
  let unembed_comp w t =
    let uu____819 =
      let uu____820 = FStar_Syntax_Subst.compress t in
      uu____820.FStar_Syntax_Syntax.n in
    match uu____819 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp;
          FStar_Syntax_Syntax.ltyp = uu____826;
          FStar_Syntax_Syntax.rng = uu____827;_}
        ->
        let uu____830 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____830
    | uu____831 ->
        (if w
         then
           (let uu____833 =
              let uu____838 =
                let uu____839 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded comp: %s" uu____839 in
              (FStar_Errors.Warning_NotEmbedded, uu____838) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____833)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp
let (e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding) =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng) in
  let unembed_env w t =
    let uu____869 =
      let uu____870 = FStar_Syntax_Subst.compress t in
      uu____870.FStar_Syntax_Syntax.n in
    match uu____869 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env;
          FStar_Syntax_Syntax.ltyp = uu____876;
          FStar_Syntax_Syntax.rng = uu____877;_}
        ->
        let uu____880 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____880
    | uu____881 ->
        (if w
         then
           (let uu____883 =
              let uu____888 =
                let uu____889 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded env: %s" uu____889 in
              (FStar_Errors.Warning_NotEmbedded, uu____888) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____883)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_env unembed_env FStar_Reflection_Data.fstar_refl_env
let (e_const :
  FStar_Reflection_Data.vconst FStar_Syntax_Embeddings.embedding) =
  let embed_const rng c =
    let r =
      match c with
      | FStar_Reflection_Data.C_Unit ->
          FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_True ->
          FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_False ->
          FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Int i ->
          let uu____910 =
            let uu____911 =
              let uu____920 =
                let uu____921 = FStar_BigInt.string_of_big_int i in
                FStar_Syntax_Util.exp_int uu____921 in
              FStar_Syntax_Syntax.as_arg uu____920 in
            [uu____911] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t uu____910
            FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____939 =
            let uu____940 =
              let uu____949 = embed FStar_Syntax_Embeddings.e_string rng s in
              FStar_Syntax_Syntax.as_arg uu____949 in
            [uu____940] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
            uu____939 FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____967 =
            let uu____968 =
              let uu____977 = embed FStar_Syntax_Embeddings.e_range rng r in
              FStar_Syntax_Syntax.as_arg uu____977 in
            [uu____968] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
            uu____967 FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____995 =
            let uu____996 =
              let uu____1005 =
                embed FStar_Syntax_Embeddings.e_string_list rng ns in
              FStar_Syntax_Syntax.as_arg uu____1005 in
            [uu____996] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
            uu____995 FStar_Range.dummyRange in
    let uu___193_1024 = r in
    {
      FStar_Syntax_Syntax.n = (uu___193_1024.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___193_1024.FStar_Syntax_Syntax.vars)
    } in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1043 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1043 with
    | (hd, args) ->
        let uu____1088 =
          let uu____1103 =
            let uu____1104 = FStar_Syntax_Util.un_uinst hd in
            uu____1104.FStar_Syntax_Syntax.n in
          (uu____1103, args) in
        (match uu____1088 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv, (i, uu____1178)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1213 = unembed' w FStar_Syntax_Embeddings.e_int i in
             FStar_Util.bind_opt uu____1213
               (fun i1 ->
                  FStar_All.pipe_left
                    (fun uu____1220 ->
                       FStar_Pervasives_Native.Some uu____1220)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (s, uu____1223)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1258 = unembed' w FStar_Syntax_Embeddings.e_string s in
             FStar_Util.bind_opt uu____1258
               (fun s1 ->
                  FStar_All.pipe_left
                    (fun uu____1265 ->
                       FStar_Pervasives_Native.Some uu____1265)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (r, uu____1268)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1303 = unembed' w FStar_Syntax_Embeddings.e_range r in
             FStar_Util.bind_opt uu____1303
               (fun r1 ->
                  FStar_All.pipe_left
                    (fun uu____1310 ->
                       FStar_Pervasives_Native.Some uu____1310)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun uu____1332 -> FStar_Pervasives_Native.Some uu____1332)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv, (ns, uu____1335)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____1370 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns in
             FStar_Util.bind_opt uu____1370
               (fun ns1 ->
                  FStar_All.pipe_left
                    (fun uu____1385 ->
                       FStar_Pervasives_Native.Some uu____1385)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____1386 ->
             (if w
              then
                (let uu____1402 =
                   let uu____1407 =
                     let uu____1408 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1408 in
                   (FStar_Errors.Warning_NotEmbedded, uu____1407) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1402)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1416 ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1429 =
            let uu____1430 =
              let uu____1439 = embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu____1439 in
            [uu____1430] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
            uu____1429 rng
      | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
          let uu____1470 =
            let uu____1471 =
              let uu____1480 = embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu____1480 in
            let uu____1481 =
              let uu____1492 =
                let uu____1501 =
                  let uu____1502 =
                    let uu____1511 =
                      let uu____1518 = e_pattern' () in
                      FStar_Syntax_Embeddings.e_tuple2 uu____1518
                        FStar_Syntax_Embeddings.e_bool in
                    FStar_Syntax_Embeddings.e_list uu____1511 in
                  embed uu____1502 rng ps in
                FStar_Syntax_Syntax.as_arg uu____1501 in
              [uu____1492] in
            uu____1471 :: uu____1481 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
            uu____1470 rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1556 =
            let uu____1557 =
              let uu____1566 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____1566 in
            [uu____1557] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
            uu____1556 rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1584 =
            let uu____1585 =
              let uu____1594 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____1594 in
            [uu____1585] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
            uu____1584 rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv, t) ->
          let uu____1613 =
            let uu____1614 =
              let uu____1623 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____1623 in
            let uu____1624 =
              let uu____1635 =
                let uu____1644 = embed e_term rng t in
                FStar_Syntax_Syntax.as_arg uu____1644 in
              [uu____1635] in
            uu____1614 :: uu____1624 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
            uu____1613 rng in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t in
      let uu____1685 = FStar_Syntax_Util.head_and_args t1 in
      match uu____1685 with
      | (hd, args) ->
          let uu____1730 =
            let uu____1743 =
              let uu____1744 = FStar_Syntax_Util.un_uinst hd in
              uu____1744.FStar_Syntax_Syntax.n in
            (uu____1743, args) in
          (match uu____1730 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (c, uu____1759)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1784 = unembed' w e_const c in
               FStar_Util.bind_opt uu____1784
                 (fun c1 ->
                    FStar_All.pipe_left
                      (fun uu____1791 ->
                         FStar_Pervasives_Native.Some uu____1791)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (f, uu____1794)::(ps, uu____1796)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1831 = unembed' w e_fv f in
               FStar_Util.bind_opt uu____1831
                 (fun f1 ->
                    let uu____1837 =
                      let uu____1846 =
                        let uu____1855 =
                          let uu____1862 = e_pattern' () in
                          FStar_Syntax_Embeddings.e_tuple2 uu____1862
                            FStar_Syntax_Embeddings.e_bool in
                        FStar_Syntax_Embeddings.e_list uu____1855 in
                      unembed' w uu____1846 ps in
                    FStar_Util.bind_opt uu____1837
                      (fun ps1 ->
                         FStar_All.pipe_left
                           (fun uu____1891 ->
                              FStar_Pervasives_Native.Some uu____1891)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (bv, uu____1900)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1925 = unembed' w e_bv bv in
               FStar_Util.bind_opt uu____1925
                 (fun bv1 ->
                    FStar_All.pipe_left
                      (fun uu____1932 ->
                         FStar_Pervasives_Native.Some uu____1932)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (bv, uu____1935)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1960 = unembed' w e_bv bv in
               FStar_Util.bind_opt uu____1960
                 (fun bv1 ->
                    FStar_All.pipe_left
                      (fun uu____1967 ->
                         FStar_Pervasives_Native.Some uu____1967)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (bv, uu____1970)::(t2, uu____1972)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____2007 = unembed' w e_bv bv in
               FStar_Util.bind_opt uu____2007
                 (fun bv1 ->
                    let uu____2013 = unembed' w e_term t2 in
                    FStar_Util.bind_opt uu____2013
                      (fun t3 ->
                         FStar_All.pipe_left
                           (fun uu____2020 ->
                              FStar_Pervasives_Native.Some uu____2020)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2021 ->
               (if w
                then
                  (let uu____2035 =
                     let uu____2040 =
                       let uu____2041 = FStar_Syntax_Print.term_to_string t1 in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2041 in
                     (FStar_Errors.Warning_NotEmbedded, uu____2040) in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2035)
                else ();
                FStar_Pervasives_Native.None)) in
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
let (e_args :
  FStar_Reflection_Data.argv Prims.list FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_list e_argv
let (e_branch_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq ->
    let uu____2064 = e_term_aq aq in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2064
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq ->
    let uu____2078 = e_term_aq aq in
    FStar_Syntax_Embeddings.e_tuple2 uu____2078 e_aqualv
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2100 =
            let uu____2101 =
              let uu____2110 = embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu____2110 in
            [uu____2101] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
            uu____2100 rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2128 =
            let uu____2129 =
              let uu____2138 = embed e_bv rng fv in
              FStar_Syntax_Syntax.as_arg uu____2138 in
            [uu____2129] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
            uu____2128 rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2156 =
            let uu____2157 =
              let uu____2166 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____2166 in
            [uu____2157] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
            uu____2156 rng
      | FStar_Reflection_Data.Tv_App (hd, a) ->
          let uu____2185 =
            let uu____2186 =
              let uu____2195 =
                let uu____2196 = e_term_aq aq in embed uu____2196 rng hd in
              FStar_Syntax_Syntax.as_arg uu____2195 in
            let uu____2199 =
              let uu____2210 =
                let uu____2219 =
                  let uu____2220 = e_argv_aq aq in embed uu____2220 rng a in
                FStar_Syntax_Syntax.as_arg uu____2219 in
              [uu____2210] in
            uu____2186 :: uu____2199 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
            uu____2185 rng
      | FStar_Reflection_Data.Tv_Abs (b, t1) ->
          let uu____2257 =
            let uu____2258 =
              let uu____2267 = embed e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu____2267 in
            let uu____2268 =
              let uu____2279 =
                let uu____2288 =
                  let uu____2289 = e_term_aq aq in embed uu____2289 rng t1 in
                FStar_Syntax_Syntax.as_arg uu____2288 in
              [uu____2279] in
            uu____2258 :: uu____2268 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
            uu____2257 rng
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          let uu____2318 =
            let uu____2319 =
              let uu____2328 = embed e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu____2328 in
            let uu____2329 =
              let uu____2340 =
                let uu____2349 = embed e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu____2349 in
              [uu____2340] in
            uu____2319 :: uu____2329 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
            uu____2318 rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2375 =
            let uu____2376 =
              let uu____2385 = embed FStar_Syntax_Embeddings.e_unit rng () in
              FStar_Syntax_Syntax.as_arg uu____2385 in
            [uu____2376] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
            uu____2375 rng
      | FStar_Reflection_Data.Tv_Refine (bv, t1) ->
          let uu____2404 =
            let uu____2405 =
              let uu____2414 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____2414 in
            let uu____2415 =
              let uu____2426 =
                let uu____2435 =
                  let uu____2436 = e_term_aq aq in embed uu____2436 rng t1 in
                FStar_Syntax_Syntax.as_arg uu____2435 in
              [uu____2426] in
            uu____2405 :: uu____2415 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
            uu____2404 rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2464 =
            let uu____2465 =
              let uu____2474 = embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu____2474 in
            [uu____2465] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
            uu____2464 rng
      | FStar_Reflection_Data.Tv_Uvar (u, d) ->
          let uu____2493 =
            let uu____2494 =
              let uu____2503 = embed FStar_Syntax_Embeddings.e_int rng u in
              FStar_Syntax_Syntax.as_arg uu____2503 in
            let uu____2504 =
              let uu____2515 =
                let uu____2524 =
                  FStar_Syntax_Util.mk_lazy (u, d)
                    FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.as_arg uu____2524 in
              [uu____2515] in
            uu____2494 :: uu____2504 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
            uu____2493 rng
      | FStar_Reflection_Data.Tv_Let (r, attrs, b, t1, t2) ->
          let uu____2562 =
            let uu____2563 =
              let uu____2572 = embed FStar_Syntax_Embeddings.e_bool rng r in
              FStar_Syntax_Syntax.as_arg uu____2572 in
            let uu____2573 =
              let uu____2584 =
                let uu____2593 =
                  let uu____2594 = FStar_Syntax_Embeddings.e_list e_term in
                  embed uu____2594 rng attrs in
                FStar_Syntax_Syntax.as_arg uu____2593 in
              let uu____2601 =
                let uu____2612 =
                  let uu____2621 = embed e_bv rng b in
                  FStar_Syntax_Syntax.as_arg uu____2621 in
                let uu____2622 =
                  let uu____2633 =
                    let uu____2642 =
                      let uu____2643 = e_term_aq aq in
                      embed uu____2643 rng t1 in
                    FStar_Syntax_Syntax.as_arg uu____2642 in
                  let uu____2646 =
                    let uu____2657 =
                      let uu____2666 =
                        let uu____2667 = e_term_aq aq in
                        embed uu____2667 rng t2 in
                      FStar_Syntax_Syntax.as_arg uu____2666 in
                    [uu____2657] in
                  uu____2633 :: uu____2646 in
                uu____2612 :: uu____2622 in
              uu____2584 :: uu____2601 in
            uu____2563 :: uu____2573 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
            uu____2562 rng
      | FStar_Reflection_Data.Tv_Match (t1, brs) ->
          let uu____2724 =
            let uu____2725 =
              let uu____2734 =
                let uu____2735 = e_term_aq aq in embed uu____2735 rng t1 in
              FStar_Syntax_Syntax.as_arg uu____2734 in
            let uu____2738 =
              let uu____2749 =
                let uu____2758 =
                  let uu____2759 =
                    let uu____2768 = e_branch_aq aq in
                    FStar_Syntax_Embeddings.e_list uu____2768 in
                  embed uu____2759 rng brs in
                FStar_Syntax_Syntax.as_arg uu____2758 in
              [uu____2749] in
            uu____2725 :: uu____2738 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
            uu____2724 rng
      | FStar_Reflection_Data.Tv_AscribedT (e, t1, tacopt) ->
          let uu____2816 =
            let uu____2817 =
              let uu____2826 =
                let uu____2827 = e_term_aq aq in embed uu____2827 rng e in
              FStar_Syntax_Syntax.as_arg uu____2826 in
            let uu____2830 =
              let uu____2841 =
                let uu____2850 =
                  let uu____2851 = e_term_aq aq in embed uu____2851 rng t1 in
                FStar_Syntax_Syntax.as_arg uu____2850 in
              let uu____2854 =
                let uu____2865 =
                  let uu____2874 =
                    let uu____2875 =
                      let uu____2880 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu____2880 in
                    embed uu____2875 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu____2874 in
                [uu____2865] in
              uu____2841 :: uu____2854 in
            uu____2817 :: uu____2830 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
            uu____2816 rng
      | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
          let uu____2924 =
            let uu____2925 =
              let uu____2934 =
                let uu____2935 = e_term_aq aq in embed uu____2935 rng e in
              FStar_Syntax_Syntax.as_arg uu____2934 in
            let uu____2938 =
              let uu____2949 =
                let uu____2958 = embed e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu____2958 in
              let uu____2959 =
                let uu____2970 =
                  let uu____2979 =
                    let uu____2980 =
                      let uu____2985 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu____2985 in
                    embed uu____2980 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu____2979 in
                [uu____2970] in
              uu____2949 :: uu____2959 in
            uu____2925 :: uu____2938 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
            uu____2924 rng
      | FStar_Reflection_Data.Tv_Unknown ->
          let uu___387_3022 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t in
          {
            FStar_Syntax_Syntax.n = (uu___387_3022.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___387_3022.FStar_Syntax_Syntax.vars)
          } in
    let unembed_term_view w t =
      let uu____3038 = FStar_Syntax_Util.head_and_args t in
      match uu____3038 with
      | (hd, args) ->
          let uu____3083 =
            let uu____3096 =
              let uu____3097 = FStar_Syntax_Util.un_uinst hd in
              uu____3097.FStar_Syntax_Syntax.n in
            (uu____3096, args) in
          (match uu____3083 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu____3112)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3137 = unembed' w e_bv b in
               FStar_Util.bind_opt uu____3137
                 (fun b1 ->
                    FStar_All.pipe_left
                      (fun uu____3144 ->
                         FStar_Pervasives_Native.Some uu____3144)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu____3147)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3172 = unembed' w e_bv b in
               FStar_Util.bind_opt uu____3172
                 (fun b1 ->
                    FStar_All.pipe_left
                      (fun uu____3179 ->
                         FStar_Pervasives_Native.Some uu____3179)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (f, uu____3182)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3207 = unembed' w e_fv f in
               FStar_Util.bind_opt uu____3207
                 (fun f1 ->
                    FStar_All.pipe_left
                      (fun uu____3214 ->
                         FStar_Pervasives_Native.Some uu____3214)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (l, uu____3217)::(r, uu____3219)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3254 = unembed' w e_term l in
               FStar_Util.bind_opt uu____3254
                 (fun l1 ->
                    let uu____3260 = unembed' w e_argv r in
                    FStar_Util.bind_opt uu____3260
                      (fun r1 ->
                         FStar_All.pipe_left
                           (fun uu____3267 ->
                              FStar_Pervasives_Native.Some uu____3267)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (b, uu____3270)::(t1, uu____3272)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3307 = unembed' w e_binder b in
               FStar_Util.bind_opt uu____3307
                 (fun b1 ->
                    let uu____3313 = unembed' w e_term t1 in
                    FStar_Util.bind_opt uu____3313
                      (fun t2 ->
                         FStar_All.pipe_left
                           (fun uu____3320 ->
                              FStar_Pervasives_Native.Some uu____3320)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (b, uu____3323)::(t1, uu____3325)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3360 = unembed' w e_binder b in
               FStar_Util.bind_opt uu____3360
                 (fun b1 ->
                    let uu____3366 = unembed' w e_comp t1 in
                    FStar_Util.bind_opt uu____3366
                      (fun c ->
                         FStar_All.pipe_left
                           (fun uu____3373 ->
                              FStar_Pervasives_Native.Some uu____3373)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu____3376)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3401 = unembed' w FStar_Syntax_Embeddings.e_unit u in
               FStar_Util.bind_opt uu____3401
                 (fun u1 ->
                    FStar_All.pipe_left
                      (fun uu____3408 ->
                         FStar_Pervasives_Native.Some uu____3408)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (b, uu____3411)::(t1, uu____3413)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3448 = unembed' w e_bv b in
               FStar_Util.bind_opt uu____3448
                 (fun b1 ->
                    let uu____3454 = unembed' w e_term t1 in
                    FStar_Util.bind_opt uu____3454
                      (fun t2 ->
                         FStar_All.pipe_left
                           (fun uu____3461 ->
                              FStar_Pervasives_Native.Some uu____3461)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (c, uu____3464)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3489 = unembed' w e_const c in
               FStar_Util.bind_opt uu____3489
                 (fun c1 ->
                    FStar_All.pipe_left
                      (fun uu____3496 ->
                         FStar_Pervasives_Native.Some uu____3496)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (u, uu____3499)::(l, uu____3501)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3536 = unembed' w FStar_Syntax_Embeddings.e_int u in
               FStar_Util.bind_opt uu____3536
                 (fun u1 ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l in
                    FStar_All.pipe_left
                      (fun uu____3545 ->
                         FStar_Pervasives_Native.Some uu____3545)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (r, uu____3548)::(attrs, uu____3550)::(b, uu____3552)::
              (t1, uu____3554)::(t2, uu____3556)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3621 = unembed' w FStar_Syntax_Embeddings.e_bool r in
               FStar_Util.bind_opt uu____3621
                 (fun r1 ->
                    let uu____3627 =
                      let uu____3632 = FStar_Syntax_Embeddings.e_list e_term in
                      unembed' w uu____3632 attrs in
                    FStar_Util.bind_opt uu____3627
                      (fun attrs1 ->
                         let uu____3646 = unembed' w e_bv b in
                         FStar_Util.bind_opt uu____3646
                           (fun b1 ->
                              let uu____3652 = unembed' w e_term t1 in
                              FStar_Util.bind_opt uu____3652
                                (fun t11 ->
                                   let uu____3658 = unembed' w e_term t2 in
                                   FStar_Util.bind_opt uu____3658
                                     (fun t21 ->
                                        FStar_All.pipe_left
                                          (fun uu____3665 ->
                                             FStar_Pervasives_Native.Some
                                               uu____3665)
                                          (FStar_Reflection_Data.Tv_Let
                                             (r1, attrs1, b1, t11, t21)))))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (t1, uu____3670)::(brs, uu____3672)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3707 = unembed' w e_term t1 in
               FStar_Util.bind_opt uu____3707
                 (fun t2 ->
                    let uu____3713 =
                      let uu____3718 =
                        FStar_Syntax_Embeddings.e_list e_branch in
                      unembed' w uu____3718 brs in
                    FStar_Util.bind_opt uu____3713
                      (fun brs1 ->
                         FStar_All.pipe_left
                           (fun uu____3733 ->
                              FStar_Pervasives_Native.Some uu____3733)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (e, uu____3738)::(t1, uu____3740)::(tacopt, uu____3742)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3787 = unembed' w e_term e in
               FStar_Util.bind_opt uu____3787
                 (fun e1 ->
                    let uu____3793 = unembed' w e_term t1 in
                    FStar_Util.bind_opt uu____3793
                      (fun t2 ->
                         let uu____3799 =
                           let uu____3804 =
                             FStar_Syntax_Embeddings.e_option e_term in
                           unembed' w uu____3804 tacopt in
                         FStar_Util.bind_opt uu____3799
                           (fun tacopt1 ->
                              FStar_All.pipe_left
                                (fun uu____3819 ->
                                   FStar_Pervasives_Native.Some uu____3819)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (e, uu____3824)::(c, uu____3826)::(tacopt, uu____3828)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3873 = unembed' w e_term e in
               FStar_Util.bind_opt uu____3873
                 (fun e1 ->
                    let uu____3879 = unembed' w e_comp c in
                    FStar_Util.bind_opt uu____3879
                      (fun c1 ->
                         let uu____3885 =
                           let uu____3890 =
                             FStar_Syntax_Embeddings.e_option e_term in
                           unembed' w uu____3890 tacopt in
                         FStar_Util.bind_opt uu____3885
                           (fun tacopt1 ->
                              FStar_All.pipe_left
                                (fun uu____3905 ->
                                   FStar_Pervasives_Native.Some uu____3905)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun uu____3925 -> FStar_Pervasives_Native.Some uu____3925)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____3926 ->
               (if w
                then
                  (let uu____3940 =
                     let uu____3945 =
                       let uu____3946 = FStar_Syntax_Print.term_to_string t in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3946 in
                     (FStar_Errors.Warning_NotEmbedded, uu____3945) in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3940)
                else ();
                FStar_Pervasives_Native.None)) in
    mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq []
let (e_lid : FStar_Ident.lid FStar_Syntax_Embeddings.embedding) =
  let embed1 rng lid =
    let uu____3969 = FStar_Ident.path_of_lid lid in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____3969 in
  let unembed w t =
    let uu____3993 = unembed' w FStar_Syntax_Embeddings.e_string_list t in
    FStar_Util.map_opt uu____3993
      (fun p -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos) in
  let uu____4006 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x -> fun r -> fun uu____4013 -> fun uu____4014 -> embed1 r x)
    (fun x -> fun w -> fun uu____4021 -> unembed w x) uu____4006
    FStar_Ident.string_of_lid FStar_Syntax_Syntax.ET_abstract
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____4036 =
      let uu____4037 =
        let uu____4046 =
          embed FStar_Syntax_Embeddings.e_string rng
            bvv.FStar_Reflection_Data.bv_ppname in
        FStar_Syntax_Syntax.as_arg uu____4046 in
      let uu____4047 =
        let uu____4058 =
          let uu____4067 =
            embed FStar_Syntax_Embeddings.e_int rng
              bvv.FStar_Reflection_Data.bv_index in
          FStar_Syntax_Syntax.as_arg uu____4067 in
        let uu____4068 =
          let uu____4079 =
            let uu____4088 =
              embed e_term rng bvv.FStar_Reflection_Data.bv_sort in
            FStar_Syntax_Syntax.as_arg uu____4088 in
          [uu____4079] in
        uu____4058 :: uu____4068 in
      uu____4037 :: uu____4047 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4036 rng in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____4137 = FStar_Syntax_Util.head_and_args t1 in
    match uu____4137 with
    | (hd, args) ->
        let uu____4182 =
          let uu____4195 =
            let uu____4196 = FStar_Syntax_Util.un_uinst hd in
            uu____4196.FStar_Syntax_Syntax.n in
          (uu____4195, args) in
        (match uu____4182 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (nm, uu____4211)::(idx, uu____4213)::(s, uu____4215)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4260 = unembed' w FStar_Syntax_Embeddings.e_string nm in
             FStar_Util.bind_opt uu____4260
               (fun nm1 ->
                  let uu____4266 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx in
                  FStar_Util.bind_opt uu____4266
                    (fun idx1 ->
                       let uu____4272 = unembed' w e_term s in
                       FStar_Util.bind_opt uu____4272
                         (fun s1 ->
                            FStar_All.pipe_left
                              (fun uu____4279 ->
                                 FStar_Pervasives_Native.Some uu____4279)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4280 ->
             (if w
              then
                (let uu____4294 =
                   let uu____4299 =
                     let uu____4300 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4300 in
                   (FStar_Errors.Warning_NotEmbedded, uu____4299) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4294)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding) =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t, md) ->
        let uu____4321 =
          let uu____4322 =
            let uu____4331 = embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu____4331 in
          let uu____4332 =
            let uu____4343 =
              let uu____4352 =
                let uu____4353 = FStar_Syntax_Embeddings.e_option e_term in
                embed uu____4353 rng md in
              FStar_Syntax_Syntax.as_arg uu____4352 in
            [uu____4343] in
          uu____4322 :: uu____4332 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
          uu____4321 rng
    | FStar_Reflection_Data.C_GTotal (t, md) ->
        let uu____4390 =
          let uu____4391 =
            let uu____4400 = embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu____4400 in
          let uu____4401 =
            let uu____4412 =
              let uu____4421 =
                let uu____4422 = FStar_Syntax_Embeddings.e_option e_term in
                embed uu____4422 rng md in
              FStar_Syntax_Syntax.as_arg uu____4421 in
            [uu____4412] in
          uu____4391 :: uu____4401 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.t
          uu____4390 rng
    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
        let uu____4456 =
          let uu____4457 =
            let uu____4466 = embed e_term rng pre in
            FStar_Syntax_Syntax.as_arg uu____4466 in
          let uu____4467 =
            let uu____4478 =
              let uu____4487 = embed e_term rng post in
              FStar_Syntax_Syntax.as_arg uu____4487 in
            let uu____4488 =
              let uu____4499 =
                let uu____4508 = embed e_term rng pats in
                FStar_Syntax_Syntax.as_arg uu____4508 in
              [uu____4499] in
            uu____4478 :: uu____4488 in
          uu____4457 :: uu____4467 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
          uu____4456 rng
    | FStar_Reflection_Data.C_Eff (us, eff, res, args) ->
        let uu____4553 =
          let uu____4554 =
            let uu____4563 = embed FStar_Syntax_Embeddings.e_unit rng () in
            FStar_Syntax_Syntax.as_arg uu____4563 in
          let uu____4564 =
            let uu____4575 =
              let uu____4584 =
                embed FStar_Syntax_Embeddings.e_string_list rng eff in
              FStar_Syntax_Syntax.as_arg uu____4584 in
            let uu____4587 =
              let uu____4598 =
                let uu____4607 = embed e_term rng res in
                FStar_Syntax_Syntax.as_arg uu____4607 in
              let uu____4608 =
                let uu____4619 =
                  let uu____4628 =
                    let uu____4629 = FStar_Syntax_Embeddings.e_list e_argv in
                    embed uu____4629 rng args in
                  FStar_Syntax_Syntax.as_arg uu____4628 in
                [uu____4619] in
              uu____4598 :: uu____4608 in
            uu____4575 :: uu____4587 in
          uu____4554 :: uu____4564 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.t uu____4553
          rng in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____4692 = FStar_Syntax_Util.head_and_args t1 in
    match uu____4692 with
    | (hd, args) ->
        let uu____4737 =
          let uu____4750 =
            let uu____4751 = FStar_Syntax_Util.un_uinst hd in
            uu____4751.FStar_Syntax_Syntax.n in
          (uu____4750, args) in
        (match uu____4737 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (t2, uu____4766)::(md, uu____4768)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4803 = unembed' w e_term t2 in
             FStar_Util.bind_opt uu____4803
               (fun t3 ->
                  let uu____4809 =
                    let uu____4814 = FStar_Syntax_Embeddings.e_option e_term in
                    unembed' w uu____4814 md in
                  FStar_Util.bind_opt uu____4809
                    (fun md1 ->
                       FStar_All.pipe_left
                         (fun uu____4829 ->
                            FStar_Pervasives_Native.Some uu____4829)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (t2, uu____4834)::(md, uu____4836)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
             ->
             let uu____4871 = unembed' w e_term t2 in
             FStar_Util.bind_opt uu____4871
               (fun t3 ->
                  let uu____4877 =
                    let uu____4882 = FStar_Syntax_Embeddings.e_option e_term in
                    unembed' w uu____4882 md in
                  FStar_Util.bind_opt uu____4877
                    (fun md1 ->
                       FStar_All.pipe_left
                         (fun uu____4897 ->
                            FStar_Pervasives_Native.Some uu____4897)
                         (FStar_Reflection_Data.C_GTotal (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (pre, uu____4902)::(post, uu____4904)::(pats, uu____4906)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4951 = unembed' w e_term pre in
             FStar_Util.bind_opt uu____4951
               (fun pre1 ->
                  let uu____4957 = unembed' w e_term post in
                  FStar_Util.bind_opt uu____4957
                    (fun post1 ->
                       let uu____4963 = unembed' w e_term pats in
                       FStar_Util.bind_opt uu____4963
                         (fun pats1 ->
                            FStar_All.pipe_left
                              (fun uu____4970 ->
                                 FStar_Pervasives_Native.Some uu____4970)
                              (FStar_Reflection_Data.C_Lemma
                                 (pre1, post1, pats1)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (us, uu____4973)::(eff, uu____4975)::(res, uu____4977)::(args1,
                                                                    uu____4979)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
             ->
             let uu____5034 = unembed' w FStar_Syntax_Embeddings.e_unit us in
             FStar_Util.bind_opt uu____5034
               (fun us1 ->
                  let uu____5040 =
                    unembed' w FStar_Syntax_Embeddings.e_string_list eff in
                  FStar_Util.bind_opt uu____5040
                    (fun eff1 ->
                       let uu____5054 = unembed' w e_term res in
                       FStar_Util.bind_opt uu____5054
                         (fun res1 ->
                            let uu____5060 =
                              let uu____5065 =
                                FStar_Syntax_Embeddings.e_list e_argv in
                              unembed' w uu____5065 args1 in
                            FStar_Util.bind_opt uu____5060
                              (fun args2 ->
                                 FStar_All.pipe_left
                                   (fun uu____5080 ->
                                      FStar_Pervasives_Native.Some uu____5080)
                                   (FStar_Reflection_Data.C_Eff
                                      ([], eff1, res1, args2))))))
         | uu____5085 ->
             (if w
              then
                (let uu____5099 =
                   let uu____5104 =
                     let uu____5105 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____5105 in
                   (FStar_Errors.Warning_NotEmbedded, uu____5104) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5099)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_comp_view unembed_comp_view
    FStar_Reflection_Data.fstar_refl_comp_view
let (e_order : FStar_Order.order FStar_Syntax_Embeddings.embedding) =
  let embed_order rng o =
    let r =
      match o with
      | FStar_Order.Lt -> FStar_Reflection_Data.ord_Lt
      | FStar_Order.Eq -> FStar_Reflection_Data.ord_Eq
      | FStar_Order.Gt -> FStar_Reflection_Data.ord_Gt in
    let uu___712_5125 = r in
    {
      FStar_Syntax_Syntax.n = (uu___712_5125.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___712_5125.FStar_Syntax_Syntax.vars)
    } in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____5144 = FStar_Syntax_Util.head_and_args t1 in
    match uu____5144 with
    | (hd, args) ->
        let uu____5189 =
          let uu____5204 =
            let uu____5205 = FStar_Syntax_Util.un_uinst hd in
            uu____5205.FStar_Syntax_Syntax.n in
          (uu____5204, args) in
        (match uu____5189 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Gt
         | uu____5277 ->
             (if w
              then
                (let uu____5293 =
                   let uu____5298 =
                     let uu____5299 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____5299 in
                   (FStar_Errors.Warning_NotEmbedded, uu____5298) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5293)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_order unembed_order FStar_Syntax_Syntax.t_order
let (e_sigelt : FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings.embedding)
  =
  let embed_sigelt rng se =
    FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng) in
  let unembed_sigelt w t =
    let uu____5329 =
      let uu____5330 = FStar_Syntax_Subst.compress t in
      uu____5330.FStar_Syntax_Syntax.n in
    match uu____5329 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt;
          FStar_Syntax_Syntax.ltyp = uu____5336;
          FStar_Syntax_Syntax.rng = uu____5337;_}
        ->
        let uu____5340 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____5340
    | uu____5341 ->
        (if w
         then
           (let uu____5343 =
              let uu____5348 =
                let uu____5349 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5349 in
              (FStar_Errors.Warning_NotEmbedded, uu____5348) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5343)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_string
      FStar_Syntax_Embeddings.e_range in
  FStar_Syntax_Embeddings.embed_as repr FStar_Ident.mk_ident
    (fun i ->
       let uu____5370 = FStar_Ident.string_of_id i in
       let uu____5371 = FStar_Ident.range_of_id i in (uu____5370, uu____5371))
    (FStar_Pervasives_Native.Some FStar_Reflection_Data.fstar_refl_ident)
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
    | FStar_Reflection_Data.Sg_Let (r, fv, univs, ty, t) ->
        let uu____5400 =
          let uu____5401 =
            let uu____5410 = embed FStar_Syntax_Embeddings.e_bool rng r in
            FStar_Syntax_Syntax.as_arg uu____5410 in
          let uu____5411 =
            let uu____5422 =
              let uu____5431 = embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu____5431 in
            let uu____5432 =
              let uu____5443 =
                let uu____5452 = embed e_univ_names rng univs in
                FStar_Syntax_Syntax.as_arg uu____5452 in
              let uu____5455 =
                let uu____5466 =
                  let uu____5475 = embed e_term rng ty in
                  FStar_Syntax_Syntax.as_arg uu____5475 in
                let uu____5476 =
                  let uu____5487 =
                    let uu____5496 = embed e_term rng t in
                    FStar_Syntax_Syntax.as_arg uu____5496 in
                  [uu____5487] in
                uu____5466 :: uu____5476 in
              uu____5443 :: uu____5455 in
            uu____5422 :: uu____5432 in
          uu____5401 :: uu____5411 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t uu____5400
          rng
    | FStar_Reflection_Data.Sg_Constructor (nm, ty) ->
        let uu____5547 =
          let uu____5548 =
            let uu____5557 =
              embed FStar_Syntax_Embeddings.e_string_list rng nm in
            FStar_Syntax_Syntax.as_arg uu____5557 in
          let uu____5560 =
            let uu____5571 =
              let uu____5580 = embed e_term rng ty in
              FStar_Syntax_Syntax.as_arg uu____5580 in
            [uu____5571] in
          uu____5548 :: uu____5560 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
          uu____5547 rng
    | FStar_Reflection_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu____5622 =
          let uu____5623 =
            let uu____5632 =
              embed FStar_Syntax_Embeddings.e_string_list rng nm in
            FStar_Syntax_Syntax.as_arg uu____5632 in
          let uu____5635 =
            let uu____5646 =
              let uu____5655 = embed e_univ_names rng univs in
              FStar_Syntax_Syntax.as_arg uu____5655 in
            let uu____5658 =
              let uu____5669 =
                let uu____5678 = embed e_binders rng bs in
                FStar_Syntax_Syntax.as_arg uu____5678 in
              let uu____5679 =
                let uu____5690 =
                  let uu____5699 = embed e_term rng t in
                  FStar_Syntax_Syntax.as_arg uu____5699 in
                let uu____5700 =
                  let uu____5711 =
                    let uu____5720 =
                      let uu____5721 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list in
                      embed uu____5721 rng dcs in
                    FStar_Syntax_Syntax.as_arg uu____5720 in
                  [uu____5711] in
                uu____5690 :: uu____5700 in
              uu____5669 :: uu____5679 in
            uu____5646 :: uu____5658 in
          uu____5623 :: uu____5635 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
          uu____5622 rng
    | FStar_Reflection_Data.Unk ->
        let uu___775_5782 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t in
        {
          FStar_Syntax_Syntax.n = (uu___775_5782.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___775_5782.FStar_Syntax_Syntax.vars)
        } in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____5799 = FStar_Syntax_Util.head_and_args t1 in
    match uu____5799 with
    | (hd, args) ->
        let uu____5844 =
          let uu____5857 =
            let uu____5858 = FStar_Syntax_Util.un_uinst hd in
            uu____5858.FStar_Syntax_Syntax.n in
          (uu____5857, args) in
        (match uu____5844 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (nm, uu____5873)::(us, uu____5875)::(bs, uu____5877)::(t2,
                                                                   uu____5879)::
            (dcs, uu____5881)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5946 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm in
             FStar_Util.bind_opt uu____5946
               (fun nm1 ->
                  let uu____5960 = unembed' w e_univ_names us in
                  FStar_Util.bind_opt uu____5960
                    (fun us1 ->
                       let uu____5974 = unembed' w e_binders bs in
                       FStar_Util.bind_opt uu____5974
                         (fun bs1 ->
                            let uu____5980 = unembed' w e_term t2 in
                            FStar_Util.bind_opt uu____5980
                              (fun t3 ->
                                 let uu____5986 =
                                   let uu____5993 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list in
                                   unembed' w uu____5993 dcs in
                                 FStar_Util.bind_opt uu____5986
                                   (fun dcs1 ->
                                      FStar_All.pipe_left
                                        (fun uu____6018 ->
                                           FStar_Pervasives_Native.Some
                                             uu____6018)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (r, uu____6027)::(fvar, uu____6029)::(univs, uu____6031)::
            (ty, uu____6033)::(t2, uu____6035)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____6100 = unembed' w FStar_Syntax_Embeddings.e_bool r in
             FStar_Util.bind_opt uu____6100
               (fun r1 ->
                  let uu____6106 = unembed' w e_fv fvar in
                  FStar_Util.bind_opt uu____6106
                    (fun fvar1 ->
                       let uu____6112 = unembed' w e_univ_names univs in
                       FStar_Util.bind_opt uu____6112
                         (fun univs1 ->
                            let uu____6126 = unembed' w e_term ty in
                            FStar_Util.bind_opt uu____6126
                              (fun ty1 ->
                                 let uu____6132 = unembed' w e_term t2 in
                                 FStar_Util.bind_opt uu____6132
                                   (fun t3 ->
                                      FStar_All.pipe_left
                                        (fun uu____6139 ->
                                           FStar_Pervasives_Native.Some
                                             uu____6139)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar1, univs1, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6157 ->
             (if w
              then
                (let uu____6171 =
                   let uu____6176 =
                     let uu____6177 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6177 in
                   (FStar_Errors.Warning_NotEmbedded, uu____6176) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6171)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_Data.fstar_refl_sigelt_view
let (e_exp : FStar_Reflection_Data.exp FStar_Syntax_Embeddings.embedding) =
  let rec embed_exp rng e =
    let r =
      match e with
      | FStar_Reflection_Data.Unit ->
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Var i ->
          let uu____6198 =
            let uu____6199 =
              let uu____6208 =
                let uu____6209 = FStar_BigInt.string_of_big_int i in
                FStar_Syntax_Util.exp_int uu____6209 in
              FStar_Syntax_Syntax.as_arg uu____6208 in
            [uu____6199] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
            uu____6198 FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1, e2) ->
          let uu____6228 =
            let uu____6229 =
              let uu____6238 = embed_exp rng e1 in
              FStar_Syntax_Syntax.as_arg uu____6238 in
            let uu____6239 =
              let uu____6250 =
                let uu____6259 = embed_exp rng e2 in
                FStar_Syntax_Syntax.as_arg uu____6259 in
              [uu____6250] in
            uu____6229 :: uu____6239 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
            uu____6228 FStar_Range.dummyRange in
    let uu___850_6284 = r in
    {
      FStar_Syntax_Syntax.n = (uu___850_6284.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___850_6284.FStar_Syntax_Syntax.vars)
    } in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____6303 = FStar_Syntax_Util.head_and_args t1 in
    match uu____6303 with
    | (hd, args) ->
        let uu____6348 =
          let uu____6361 =
            let uu____6362 = FStar_Syntax_Util.un_uinst hd in
            uu____6362.FStar_Syntax_Syntax.n in
          (uu____6361, args) in
        (match uu____6348 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv, (i, uu____6392)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6417 = unembed' w FStar_Syntax_Embeddings.e_int i in
             FStar_Util.bind_opt uu____6417
               (fun i1 ->
                  FStar_All.pipe_left
                    (fun uu____6424 ->
                       FStar_Pervasives_Native.Some uu____6424)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (e1, uu____6427)::(e2, uu____6429)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6464 = unembed_exp w e1 in
             FStar_Util.bind_opt uu____6464
               (fun e11 ->
                  let uu____6470 = unembed_exp w e2 in
                  FStar_Util.bind_opt uu____6470
                    (fun e21 ->
                       FStar_All.pipe_left
                         (fun uu____6477 ->
                            FStar_Pervasives_Native.Some uu____6477)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6478 ->
             (if w
              then
                (let uu____6492 =
                   let uu____6497 =
                     let uu____6498 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6498 in
                   (FStar_Errors.Warning_NotEmbedded, uu____6497) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6492)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_Syntax_Embeddings.embedding) = e_term
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_attribute
let (e_qualifier :
  FStar_Reflection_Data.qualifier FStar_Syntax_Embeddings.embedding) =
  let embed1 rng q =
    let r =
      match q with
      | FStar_Reflection_Data.Assumption ->
          FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.t
      | FStar_Reflection_Data.New ->
          FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Private ->
          FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Unfold_for_unification_and_vcgen ->
          FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Visible_default ->
          FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Irreducible ->
          FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Inline_for_extraction ->
          FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.t
      | FStar_Reflection_Data.NoExtract ->
          FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Noeq ->
          FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Unopteq ->
          FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.t
      | FStar_Reflection_Data.TotalEffect ->
          FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Logic ->
          FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Reifiable ->
          FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.t
      | FStar_Reflection_Data.ExceptionConstructor ->
          FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.t
      | FStar_Reflection_Data.HasMaskedEffect ->
          FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Effect ->
          FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.t
      | FStar_Reflection_Data.OnlyName ->
          FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Reflectable l ->
          let uu____6527 =
            let uu____6528 =
              let uu____6537 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu____6537 in
            [uu____6528] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
            uu____6527 FStar_Range.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu____6555 =
            let uu____6556 =
              let uu____6565 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu____6565 in
            [uu____6556] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
            uu____6555 FStar_Range.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu____6583 =
            let uu____6584 =
              let uu____6593 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu____6593 in
            [uu____6584] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
            uu____6583 FStar_Range.dummyRange
      | FStar_Reflection_Data.Projector (l, i) ->
          let uu____6612 =
            let uu____6613 =
              let uu____6622 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu____6622 in
            let uu____6623 =
              let uu____6634 =
                let uu____6643 = embed e_ident rng i in
                FStar_Syntax_Syntax.as_arg uu____6643 in
              [uu____6634] in
            uu____6613 :: uu____6623 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
            uu____6612 FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordType (ids1, ids2) ->
          let uu____6678 =
            let uu____6679 =
              let uu____6688 =
                let uu____6689 = FStar_Syntax_Embeddings.e_list e_ident in
                embed uu____6689 rng ids1 in
              FStar_Syntax_Syntax.as_arg uu____6688 in
            let uu____6696 =
              let uu____6707 =
                let uu____6716 =
                  let uu____6717 = FStar_Syntax_Embeddings.e_list e_ident in
                  embed uu____6717 rng ids2 in
                FStar_Syntax_Syntax.as_arg uu____6716 in
              [uu____6707] in
            uu____6679 :: uu____6696 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
            uu____6678 FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1, ids2) ->
          let uu____6758 =
            let uu____6759 =
              let uu____6768 =
                let uu____6769 = FStar_Syntax_Embeddings.e_list e_ident in
                embed uu____6769 rng ids1 in
              FStar_Syntax_Syntax.as_arg uu____6768 in
            let uu____6776 =
              let uu____6787 =
                let uu____6796 =
                  let uu____6797 = FStar_Syntax_Embeddings.e_list e_ident in
                  embed uu____6797 rng ids2 in
                FStar_Syntax_Syntax.as_arg uu____6796 in
              [uu____6787] in
            uu____6759 :: uu____6776 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
            uu____6758 FStar_Range.dummyRange in
    let uu___925_6828 = r in
    {
      FStar_Syntax_Syntax.n = (uu___925_6828.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___925_6828.FStar_Syntax_Syntax.vars)
    } in
  let unembed w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____6847 = FStar_Syntax_Util.head_and_args t1 in
    match uu____6847 with
    | (hd, args) ->
        let uu____6892 =
          let uu____6905 =
            let uu____6906 = FStar_Syntax_Util.un_uinst hd in
            uu____6906.FStar_Syntax_Syntax.n in
          (uu____6905, args) in
        (match uu____6892 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Assumption
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.New
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Private
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.Unfold_for_unification_and_vcgen
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.Visible_default
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_Data.Irreducible
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.Inline_for_extraction
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.NoExtract
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Noeq
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unopteq
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_Data.TotalEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Logic
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Reifiable
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.ExceptionConstructor
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.HasMaskedEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Effect
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.OnlyName
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____7176)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7201 = unembed' w e_lid l in
             FStar_Util.bind_opt uu____7201
               (fun l1 ->
                  FStar_All.pipe_left
                    (fun uu____7208 ->
                       FStar_Pervasives_Native.Some uu____7208)
                    (FStar_Reflection_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____7211)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7236 = unembed' w e_lid l in
             FStar_Util.bind_opt uu____7236
               (fun l1 ->
                  FStar_All.pipe_left
                    (fun uu____7243 ->
                       FStar_Pervasives_Native.Some uu____7243)
                    (FStar_Reflection_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____7246)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7271 = unembed' w e_lid l in
             FStar_Util.bind_opt uu____7271
               (fun l1 ->
                  FStar_All.pipe_left
                    (fun uu____7278 ->
                       FStar_Pervasives_Native.Some uu____7278)
                    (FStar_Reflection_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (l, uu____7281)::(i, uu____7283)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7318 = unembed' w e_lid l in
             FStar_Util.bind_opt uu____7318
               (fun l1 ->
                  let uu____7324 = unembed' w e_ident i in
                  FStar_Util.bind_opt uu____7324
                    (fun i1 ->
                       FStar_All.pipe_left
                         (fun uu____7331 ->
                            FStar_Pervasives_Native.Some uu____7331)
                         (FStar_Reflection_Data.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (ids1, uu____7334)::(ids2, uu____7336)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7371 =
               let uu____7376 = FStar_Syntax_Embeddings.e_list e_ident in
               unembed' w uu____7376 ids1 in
             FStar_Util.bind_opt uu____7371
               (fun ids11 ->
                  let uu____7390 =
                    let uu____7395 = FStar_Syntax_Embeddings.e_list e_ident in
                    unembed' w uu____7395 ids2 in
                  FStar_Util.bind_opt uu____7390
                    (fun ids21 ->
                       FStar_All.pipe_left
                         (fun uu____7410 ->
                            FStar_Pervasives_Native.Some uu____7410)
                         (FStar_Reflection_Data.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (ids1, uu____7417)::(ids2, uu____7419)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____7454 =
               let uu____7459 = FStar_Syntax_Embeddings.e_list e_ident in
               unembed' w uu____7459 ids1 in
             FStar_Util.bind_opt uu____7454
               (fun ids11 ->
                  let uu____7473 =
                    let uu____7478 = FStar_Syntax_Embeddings.e_list e_ident in
                    unembed' w uu____7478 ids2 in
                  FStar_Util.bind_opt uu____7473
                    (fun ids21 ->
                       FStar_All.pipe_left
                         (fun uu____7493 ->
                            FStar_Pervasives_Native.Some uu____7493)
                         (FStar_Reflection_Data.RecordConstructor
                            (ids11, ids21))))
         | uu____7498 ->
             (if w
              then
                (let uu____7512 =
                   let uu____7517 =
                     let uu____7518 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____7518 in
                   (FStar_Errors.Warning_NotEmbedded, uu____7517) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7512)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed1 unembed FStar_Reflection_Data.fstar_refl_qualifier
let (e_qualifiers :
  FStar_Reflection_Data.qualifier Prims.list
    FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_qualifier
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu____7530 =
      let uu____7531 =
        let uu____7540 =
          let uu____7541 = FStar_Reflection_Basic.inspect_bv bv in
          embed e_bv_view i.FStar_Syntax_Syntax.rng uu____7541 in
        FStar_Syntax_Syntax.as_arg uu____7540 in
      [uu____7531] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
      uu____7530 i.FStar_Syntax_Syntax.rng
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu____7564 = FStar_Reflection_Basic.inspect_binder binder in
    match uu____7564 with
    | (bv, aq) ->
        let uu____7571 =
          let uu____7572 =
            let uu____7581 = embed e_bv i.FStar_Syntax_Syntax.rng bv in
            FStar_Syntax_Syntax.as_arg uu____7581 in
          let uu____7582 =
            let uu____7593 =
              let uu____7602 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq in
              FStar_Syntax_Syntax.as_arg uu____7602 in
            [uu____7593] in
          uu____7572 :: uu____7582 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
          uu____7571 i.FStar_Syntax_Syntax.rng
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu____7633 =
      let uu____7634 =
        let uu____7643 =
          let uu____7644 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string in
          let uu____7649 = FStar_Reflection_Basic.inspect_fv fv in
          embed uu____7644 i.FStar_Syntax_Syntax.rng uu____7649 in
        FStar_Syntax_Syntax.as_arg uu____7643 in
      [uu____7634] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
      uu____7633 i.FStar_Syntax_Syntax.rng
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu____7676 =
      let uu____7677 =
        let uu____7686 =
          let uu____7687 = FStar_Reflection_Basic.inspect_comp comp in
          embed e_comp_view i.FStar_Syntax_Syntax.rng uu____7687 in
        FStar_Syntax_Syntax.as_arg uu____7686 in
      [uu____7677] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
      uu____7676 i.FStar_Syntax_Syntax.rng
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_unit
let (unfold_lazy_optionstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_unit
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu____7720 =
      let uu____7721 =
        let uu____7730 =
          let uu____7731 = FStar_Reflection_Basic.inspect_sigelt sigelt in
          embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____7731 in
        FStar_Syntax_Syntax.as_arg uu____7730 in
      [uu____7721] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
      uu____7720 i.FStar_Syntax_Syntax.rng