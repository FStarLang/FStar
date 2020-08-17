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
            uu____513 FStar_Range.dummyRange
      | FStar_Reflection_Data.Q_Meta_attr t ->
          let uu____541 =
            let uu____542 =
              let uu____551 = embed e_term rng t in
              FStar_Syntax_Syntax.as_arg uu____551 in
            [uu____542] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Q_Meta_attr.FStar_Reflection_Data.t
            uu____541 FStar_Range.dummyRange in
    let uu___106_568 = r in
    {
      FStar_Syntax_Syntax.n = (uu___106_568.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___106_568.FStar_Syntax_Syntax.vars)
    } in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____587 = FStar_Syntax_Util.head_and_args t1 in
    match uu____587 with
    | (hd, args) ->
        let uu____632 =
          let uu____647 =
            let uu____648 = FStar_Syntax_Util.un_uinst hd in
            uu____648.FStar_Syntax_Syntax.n in
          (uu____647, args) in
        (match uu____632 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv, (t2, uu____703)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____738 = unembed' w e_term t2 in
             FStar_Util.bind_opt uu____738
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (t2, uu____745)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta_attr.FStar_Reflection_Data.lid
             ->
             let uu____780 = unembed' w e_term t2 in
             FStar_Util.bind_opt uu____780
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta_attr t3))
         | uu____785 ->
             (if w
              then
                (let uu____801 =
                   let uu____806 =
                     let uu____807 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____807 in
                   (FStar_Errors.Warning_NotEmbedded, uu____806) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____801)
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
    let uu____839 =
      let uu____840 = FStar_Syntax_Subst.compress t in
      uu____840.FStar_Syntax_Syntax.n in
    match uu____839 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar;
          FStar_Syntax_Syntax.ltyp = uu____846;
          FStar_Syntax_Syntax.rng = uu____847;_}
        ->
        let uu____850 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____850
    | uu____851 ->
        (if w
         then
           (let uu____853 =
              let uu____858 =
                let uu____859 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____859 in
              (FStar_Errors.Warning_NotEmbedded, uu____858) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____853)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv
let (e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding) =
  let embed_comp rng c =
    FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng) in
  let unembed_comp w t =
    let uu____889 =
      let uu____890 = FStar_Syntax_Subst.compress t in
      uu____890.FStar_Syntax_Syntax.n in
    match uu____889 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp;
          FStar_Syntax_Syntax.ltyp = uu____896;
          FStar_Syntax_Syntax.rng = uu____897;_}
        ->
        let uu____900 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____900
    | uu____901 ->
        (if w
         then
           (let uu____903 =
              let uu____908 =
                let uu____909 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded comp: %s" uu____909 in
              (FStar_Errors.Warning_NotEmbedded, uu____908) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____903)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp
let (e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding) =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng) in
  let unembed_env w t =
    let uu____939 =
      let uu____940 = FStar_Syntax_Subst.compress t in
      uu____940.FStar_Syntax_Syntax.n in
    match uu____939 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env;
          FStar_Syntax_Syntax.ltyp = uu____946;
          FStar_Syntax_Syntax.rng = uu____947;_}
        ->
        let uu____950 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____950
    | uu____951 ->
        (if w
         then
           (let uu____953 =
              let uu____958 =
                let uu____959 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded env: %s" uu____959 in
              (FStar_Errors.Warning_NotEmbedded, uu____958) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____953)
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
          let uu____980 =
            let uu____981 =
              let uu____990 =
                let uu____991 = FStar_BigInt.string_of_big_int i in
                FStar_Syntax_Util.exp_int uu____991 in
              FStar_Syntax_Syntax.as_arg uu____990 in
            [uu____981] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t uu____980
            FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____1009 =
            let uu____1010 =
              let uu____1019 = embed FStar_Syntax_Embeddings.e_string rng s in
              FStar_Syntax_Syntax.as_arg uu____1019 in
            [uu____1010] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
            uu____1009 FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____1037 =
            let uu____1038 =
              let uu____1047 = embed FStar_Syntax_Embeddings.e_range rng r in
              FStar_Syntax_Syntax.as_arg uu____1047 in
            [uu____1038] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
            uu____1037 FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____1065 =
            let uu____1066 =
              let uu____1075 =
                embed FStar_Syntax_Embeddings.e_string_list rng ns in
              FStar_Syntax_Syntax.as_arg uu____1075 in
            [uu____1066] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
            uu____1065 FStar_Range.dummyRange in
    let uu___203_1094 = r in
    {
      FStar_Syntax_Syntax.n = (uu___203_1094.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___203_1094.FStar_Syntax_Syntax.vars)
    } in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1113 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1113 with
    | (hd, args) ->
        let uu____1158 =
          let uu____1173 =
            let uu____1174 = FStar_Syntax_Util.un_uinst hd in
            uu____1174.FStar_Syntax_Syntax.n in
          (uu____1173, args) in
        (match uu____1158 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv, (i, uu____1248)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1283 = unembed' w FStar_Syntax_Embeddings.e_int i in
             FStar_Util.bind_opt uu____1283
               (fun i1 ->
                  FStar_All.pipe_left
                    (fun uu____1290 ->
                       FStar_Pervasives_Native.Some uu____1290)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (s, uu____1293)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1328 = unembed' w FStar_Syntax_Embeddings.e_string s in
             FStar_Util.bind_opt uu____1328
               (fun s1 ->
                  FStar_All.pipe_left
                    (fun uu____1335 ->
                       FStar_Pervasives_Native.Some uu____1335)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (r, uu____1338)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1373 = unembed' w FStar_Syntax_Embeddings.e_range r in
             FStar_Util.bind_opt uu____1373
               (fun r1 ->
                  FStar_All.pipe_left
                    (fun uu____1380 ->
                       FStar_Pervasives_Native.Some uu____1380)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun uu____1402 -> FStar_Pervasives_Native.Some uu____1402)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv, (ns, uu____1405)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____1440 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns in
             FStar_Util.bind_opt uu____1440
               (fun ns1 ->
                  FStar_All.pipe_left
                    (fun uu____1455 ->
                       FStar_Pervasives_Native.Some uu____1455)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____1456 ->
             (if w
              then
                (let uu____1472 =
                   let uu____1477 =
                     let uu____1478 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1478 in
                   (FStar_Errors.Warning_NotEmbedded, uu____1477) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1472)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1486 ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1499 =
            let uu____1500 =
              let uu____1509 = embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu____1509 in
            [uu____1500] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
            uu____1499 rng
      | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
          let uu____1540 =
            let uu____1541 =
              let uu____1550 = embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu____1550 in
            let uu____1551 =
              let uu____1562 =
                let uu____1571 =
                  let uu____1572 =
                    let uu____1581 =
                      let uu____1588 = e_pattern' () in
                      FStar_Syntax_Embeddings.e_tuple2 uu____1588
                        FStar_Syntax_Embeddings.e_bool in
                    FStar_Syntax_Embeddings.e_list uu____1581 in
                  embed uu____1572 rng ps in
                FStar_Syntax_Syntax.as_arg uu____1571 in
              [uu____1562] in
            uu____1541 :: uu____1551 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
            uu____1540 rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1626 =
            let uu____1627 =
              let uu____1636 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____1636 in
            [uu____1627] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
            uu____1626 rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1654 =
            let uu____1655 =
              let uu____1664 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____1664 in
            [uu____1655] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
            uu____1654 rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv, t) ->
          let uu____1683 =
            let uu____1684 =
              let uu____1693 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____1693 in
            let uu____1694 =
              let uu____1705 =
                let uu____1714 = embed e_term rng t in
                FStar_Syntax_Syntax.as_arg uu____1714 in
              [uu____1705] in
            uu____1684 :: uu____1694 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
            uu____1683 rng in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t in
      let uu____1755 = FStar_Syntax_Util.head_and_args t1 in
      match uu____1755 with
      | (hd, args) ->
          let uu____1800 =
            let uu____1813 =
              let uu____1814 = FStar_Syntax_Util.un_uinst hd in
              uu____1814.FStar_Syntax_Syntax.n in
            (uu____1813, args) in
          (match uu____1800 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (c, uu____1829)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1854 = unembed' w e_const c in
               FStar_Util.bind_opt uu____1854
                 (fun c1 ->
                    FStar_All.pipe_left
                      (fun uu____1861 ->
                         FStar_Pervasives_Native.Some uu____1861)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (f, uu____1864)::(ps, uu____1866)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1901 = unembed' w e_fv f in
               FStar_Util.bind_opt uu____1901
                 (fun f1 ->
                    let uu____1907 =
                      let uu____1916 =
                        let uu____1925 =
                          let uu____1932 = e_pattern' () in
                          FStar_Syntax_Embeddings.e_tuple2 uu____1932
                            FStar_Syntax_Embeddings.e_bool in
                        FStar_Syntax_Embeddings.e_list uu____1925 in
                      unembed' w uu____1916 ps in
                    FStar_Util.bind_opt uu____1907
                      (fun ps1 ->
                         FStar_All.pipe_left
                           (fun uu____1961 ->
                              FStar_Pervasives_Native.Some uu____1961)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (bv, uu____1970)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1995 = unembed' w e_bv bv in
               FStar_Util.bind_opt uu____1995
                 (fun bv1 ->
                    FStar_All.pipe_left
                      (fun uu____2002 ->
                         FStar_Pervasives_Native.Some uu____2002)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (bv, uu____2005)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____2030 = unembed' w e_bv bv in
               FStar_Util.bind_opt uu____2030
                 (fun bv1 ->
                    FStar_All.pipe_left
                      (fun uu____2037 ->
                         FStar_Pervasives_Native.Some uu____2037)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (bv, uu____2040)::(t2, uu____2042)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____2077 = unembed' w e_bv bv in
               FStar_Util.bind_opt uu____2077
                 (fun bv1 ->
                    let uu____2083 = unembed' w e_term t2 in
                    FStar_Util.bind_opt uu____2083
                      (fun t3 ->
                         FStar_All.pipe_left
                           (fun uu____2090 ->
                              FStar_Pervasives_Native.Some uu____2090)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2091 ->
               (if w
                then
                  (let uu____2105 =
                     let uu____2110 =
                       let uu____2111 = FStar_Syntax_Print.term_to_string t1 in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2111 in
                     (FStar_Errors.Warning_NotEmbedded, uu____2110) in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2105)
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
    let uu____2134 = e_term_aq aq in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2134
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq ->
    let uu____2148 = e_term_aq aq in
    FStar_Syntax_Embeddings.e_tuple2 uu____2148 e_aqualv
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2170 =
            let uu____2171 =
              let uu____2180 = embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu____2180 in
            [uu____2171] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
            uu____2170 rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2198 =
            let uu____2199 =
              let uu____2208 = embed e_bv rng fv in
              FStar_Syntax_Syntax.as_arg uu____2208 in
            [uu____2199] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
            uu____2198 rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2226 =
            let uu____2227 =
              let uu____2236 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____2236 in
            [uu____2227] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
            uu____2226 rng
      | FStar_Reflection_Data.Tv_App (hd, a) ->
          let uu____2255 =
            let uu____2256 =
              let uu____2265 =
                let uu____2266 = e_term_aq aq in embed uu____2266 rng hd in
              FStar_Syntax_Syntax.as_arg uu____2265 in
            let uu____2269 =
              let uu____2280 =
                let uu____2289 =
                  let uu____2290 = e_argv_aq aq in embed uu____2290 rng a in
                FStar_Syntax_Syntax.as_arg uu____2289 in
              [uu____2280] in
            uu____2256 :: uu____2269 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
            uu____2255 rng
      | FStar_Reflection_Data.Tv_Abs (b, t1) ->
          let uu____2327 =
            let uu____2328 =
              let uu____2337 = embed e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu____2337 in
            let uu____2338 =
              let uu____2349 =
                let uu____2358 =
                  let uu____2359 = e_term_aq aq in embed uu____2359 rng t1 in
                FStar_Syntax_Syntax.as_arg uu____2358 in
              [uu____2349] in
            uu____2328 :: uu____2338 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
            uu____2327 rng
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          let uu____2388 =
            let uu____2389 =
              let uu____2398 = embed e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu____2398 in
            let uu____2399 =
              let uu____2410 =
                let uu____2419 = embed e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu____2419 in
              [uu____2410] in
            uu____2389 :: uu____2399 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
            uu____2388 rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2445 =
            let uu____2446 =
              let uu____2455 = embed FStar_Syntax_Embeddings.e_unit rng () in
              FStar_Syntax_Syntax.as_arg uu____2455 in
            [uu____2446] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
            uu____2445 rng
      | FStar_Reflection_Data.Tv_Refine (bv, t1) ->
          let uu____2474 =
            let uu____2475 =
              let uu____2484 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu____2484 in
            let uu____2485 =
              let uu____2496 =
                let uu____2505 =
                  let uu____2506 = e_term_aq aq in embed uu____2506 rng t1 in
                FStar_Syntax_Syntax.as_arg uu____2505 in
              [uu____2496] in
            uu____2475 :: uu____2485 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
            uu____2474 rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2534 =
            let uu____2535 =
              let uu____2544 = embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu____2544 in
            [uu____2535] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
            uu____2534 rng
      | FStar_Reflection_Data.Tv_Uvar (u, d) ->
          let uu____2563 =
            let uu____2564 =
              let uu____2573 = embed FStar_Syntax_Embeddings.e_int rng u in
              FStar_Syntax_Syntax.as_arg uu____2573 in
            let uu____2574 =
              let uu____2585 =
                let uu____2594 =
                  FStar_Syntax_Util.mk_lazy (u, d)
                    FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.as_arg uu____2594 in
              [uu____2585] in
            uu____2564 :: uu____2574 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
            uu____2563 rng
      | FStar_Reflection_Data.Tv_Let (r, attrs, b, t1, t2) ->
          let uu____2632 =
            let uu____2633 =
              let uu____2642 = embed FStar_Syntax_Embeddings.e_bool rng r in
              FStar_Syntax_Syntax.as_arg uu____2642 in
            let uu____2643 =
              let uu____2654 =
                let uu____2663 =
                  let uu____2664 = FStar_Syntax_Embeddings.e_list e_term in
                  embed uu____2664 rng attrs in
                FStar_Syntax_Syntax.as_arg uu____2663 in
              let uu____2671 =
                let uu____2682 =
                  let uu____2691 = embed e_bv rng b in
                  FStar_Syntax_Syntax.as_arg uu____2691 in
                let uu____2692 =
                  let uu____2703 =
                    let uu____2712 =
                      let uu____2713 = e_term_aq aq in
                      embed uu____2713 rng t1 in
                    FStar_Syntax_Syntax.as_arg uu____2712 in
                  let uu____2716 =
                    let uu____2727 =
                      let uu____2736 =
                        let uu____2737 = e_term_aq aq in
                        embed uu____2737 rng t2 in
                      FStar_Syntax_Syntax.as_arg uu____2736 in
                    [uu____2727] in
                  uu____2703 :: uu____2716 in
                uu____2682 :: uu____2692 in
              uu____2654 :: uu____2671 in
            uu____2633 :: uu____2643 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
            uu____2632 rng
      | FStar_Reflection_Data.Tv_Match (t1, brs) ->
          let uu____2794 =
            let uu____2795 =
              let uu____2804 =
                let uu____2805 = e_term_aq aq in embed uu____2805 rng t1 in
              FStar_Syntax_Syntax.as_arg uu____2804 in
            let uu____2808 =
              let uu____2819 =
                let uu____2828 =
                  let uu____2829 =
                    let uu____2838 = e_branch_aq aq in
                    FStar_Syntax_Embeddings.e_list uu____2838 in
                  embed uu____2829 rng brs in
                FStar_Syntax_Syntax.as_arg uu____2828 in
              [uu____2819] in
            uu____2795 :: uu____2808 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
            uu____2794 rng
      | FStar_Reflection_Data.Tv_AscribedT (e, t1, tacopt) ->
          let uu____2886 =
            let uu____2887 =
              let uu____2896 =
                let uu____2897 = e_term_aq aq in embed uu____2897 rng e in
              FStar_Syntax_Syntax.as_arg uu____2896 in
            let uu____2900 =
              let uu____2911 =
                let uu____2920 =
                  let uu____2921 = e_term_aq aq in embed uu____2921 rng t1 in
                FStar_Syntax_Syntax.as_arg uu____2920 in
              let uu____2924 =
                let uu____2935 =
                  let uu____2944 =
                    let uu____2945 =
                      let uu____2950 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu____2950 in
                    embed uu____2945 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu____2944 in
                [uu____2935] in
              uu____2911 :: uu____2924 in
            uu____2887 :: uu____2900 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
            uu____2886 rng
      | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
          let uu____2994 =
            let uu____2995 =
              let uu____3004 =
                let uu____3005 = e_term_aq aq in embed uu____3005 rng e in
              FStar_Syntax_Syntax.as_arg uu____3004 in
            let uu____3008 =
              let uu____3019 =
                let uu____3028 = embed e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu____3028 in
              let uu____3029 =
                let uu____3040 =
                  let uu____3049 =
                    let uu____3050 =
                      let uu____3055 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu____3055 in
                    embed uu____3050 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu____3049 in
                [uu____3040] in
              uu____3019 :: uu____3029 in
            uu____2995 :: uu____3008 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
            uu____2994 rng
      | FStar_Reflection_Data.Tv_Unknown ->
          let uu___397_3092 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t in
          {
            FStar_Syntax_Syntax.n = (uu___397_3092.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___397_3092.FStar_Syntax_Syntax.vars)
          } in
    let unembed_term_view w t =
      let uu____3108 = FStar_Syntax_Util.head_and_args t in
      match uu____3108 with
      | (hd, args) ->
          let uu____3153 =
            let uu____3166 =
              let uu____3167 = FStar_Syntax_Util.un_uinst hd in
              uu____3167.FStar_Syntax_Syntax.n in
            (uu____3166, args) in
          (match uu____3153 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu____3182)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3207 = unembed' w e_bv b in
               FStar_Util.bind_opt uu____3207
                 (fun b1 ->
                    FStar_All.pipe_left
                      (fun uu____3214 ->
                         FStar_Pervasives_Native.Some uu____3214)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu____3217)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3242 = unembed' w e_bv b in
               FStar_Util.bind_opt uu____3242
                 (fun b1 ->
                    FStar_All.pipe_left
                      (fun uu____3249 ->
                         FStar_Pervasives_Native.Some uu____3249)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (f, uu____3252)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3277 = unembed' w e_fv f in
               FStar_Util.bind_opt uu____3277
                 (fun f1 ->
                    FStar_All.pipe_left
                      (fun uu____3284 ->
                         FStar_Pervasives_Native.Some uu____3284)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (l, uu____3287)::(r, uu____3289)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3324 = unembed' w e_term l in
               FStar_Util.bind_opt uu____3324
                 (fun l1 ->
                    let uu____3330 = unembed' w e_argv r in
                    FStar_Util.bind_opt uu____3330
                      (fun r1 ->
                         FStar_All.pipe_left
                           (fun uu____3337 ->
                              FStar_Pervasives_Native.Some uu____3337)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (b, uu____3340)::(t1, uu____3342)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3377 = unembed' w e_binder b in
               FStar_Util.bind_opt uu____3377
                 (fun b1 ->
                    let uu____3383 = unembed' w e_term t1 in
                    FStar_Util.bind_opt uu____3383
                      (fun t2 ->
                         FStar_All.pipe_left
                           (fun uu____3390 ->
                              FStar_Pervasives_Native.Some uu____3390)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (b, uu____3393)::(t1, uu____3395)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3430 = unembed' w e_binder b in
               FStar_Util.bind_opt uu____3430
                 (fun b1 ->
                    let uu____3436 = unembed' w e_comp t1 in
                    FStar_Util.bind_opt uu____3436
                      (fun c ->
                         FStar_All.pipe_left
                           (fun uu____3443 ->
                              FStar_Pervasives_Native.Some uu____3443)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu____3446)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3471 = unembed' w FStar_Syntax_Embeddings.e_unit u in
               FStar_Util.bind_opt uu____3471
                 (fun u1 ->
                    FStar_All.pipe_left
                      (fun uu____3478 ->
                         FStar_Pervasives_Native.Some uu____3478)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (b, uu____3481)::(t1, uu____3483)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3518 = unembed' w e_bv b in
               FStar_Util.bind_opt uu____3518
                 (fun b1 ->
                    let uu____3524 = unembed' w e_term t1 in
                    FStar_Util.bind_opt uu____3524
                      (fun t2 ->
                         FStar_All.pipe_left
                           (fun uu____3531 ->
                              FStar_Pervasives_Native.Some uu____3531)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (c, uu____3534)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3559 = unembed' w e_const c in
               FStar_Util.bind_opt uu____3559
                 (fun c1 ->
                    FStar_All.pipe_left
                      (fun uu____3566 ->
                         FStar_Pervasives_Native.Some uu____3566)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (u, uu____3569)::(l, uu____3571)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3606 = unembed' w FStar_Syntax_Embeddings.e_int u in
               FStar_Util.bind_opt uu____3606
                 (fun u1 ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l in
                    FStar_All.pipe_left
                      (fun uu____3615 ->
                         FStar_Pervasives_Native.Some uu____3615)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (r, uu____3618)::(attrs, uu____3620)::(b, uu____3622)::
              (t1, uu____3624)::(t2, uu____3626)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3691 = unembed' w FStar_Syntax_Embeddings.e_bool r in
               FStar_Util.bind_opt uu____3691
                 (fun r1 ->
                    let uu____3697 =
                      let uu____3702 = FStar_Syntax_Embeddings.e_list e_term in
                      unembed' w uu____3702 attrs in
                    FStar_Util.bind_opt uu____3697
                      (fun attrs1 ->
                         let uu____3716 = unembed' w e_bv b in
                         FStar_Util.bind_opt uu____3716
                           (fun b1 ->
                              let uu____3722 = unembed' w e_term t1 in
                              FStar_Util.bind_opt uu____3722
                                (fun t11 ->
                                   let uu____3728 = unembed' w e_term t2 in
                                   FStar_Util.bind_opt uu____3728
                                     (fun t21 ->
                                        FStar_All.pipe_left
                                          (fun uu____3735 ->
                                             FStar_Pervasives_Native.Some
                                               uu____3735)
                                          (FStar_Reflection_Data.Tv_Let
                                             (r1, attrs1, b1, t11, t21)))))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (t1, uu____3740)::(brs, uu____3742)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3777 = unembed' w e_term t1 in
               FStar_Util.bind_opt uu____3777
                 (fun t2 ->
                    let uu____3783 =
                      let uu____3788 =
                        FStar_Syntax_Embeddings.e_list e_branch in
                      unembed' w uu____3788 brs in
                    FStar_Util.bind_opt uu____3783
                      (fun brs1 ->
                         FStar_All.pipe_left
                           (fun uu____3803 ->
                              FStar_Pervasives_Native.Some uu____3803)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (e, uu____3808)::(t1, uu____3810)::(tacopt, uu____3812)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3857 = unembed' w e_term e in
               FStar_Util.bind_opt uu____3857
                 (fun e1 ->
                    let uu____3863 = unembed' w e_term t1 in
                    FStar_Util.bind_opt uu____3863
                      (fun t2 ->
                         let uu____3869 =
                           let uu____3874 =
                             FStar_Syntax_Embeddings.e_option e_term in
                           unembed' w uu____3874 tacopt in
                         FStar_Util.bind_opt uu____3869
                           (fun tacopt1 ->
                              FStar_All.pipe_left
                                (fun uu____3889 ->
                                   FStar_Pervasives_Native.Some uu____3889)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (e, uu____3894)::(c, uu____3896)::(tacopt, uu____3898)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3943 = unembed' w e_term e in
               FStar_Util.bind_opt uu____3943
                 (fun e1 ->
                    let uu____3949 = unembed' w e_comp c in
                    FStar_Util.bind_opt uu____3949
                      (fun c1 ->
                         let uu____3955 =
                           let uu____3960 =
                             FStar_Syntax_Embeddings.e_option e_term in
                           unembed' w uu____3960 tacopt in
                         FStar_Util.bind_opt uu____3955
                           (fun tacopt1 ->
                              FStar_All.pipe_left
                                (fun uu____3975 ->
                                   FStar_Pervasives_Native.Some uu____3975)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun uu____3995 -> FStar_Pervasives_Native.Some uu____3995)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____3996 ->
               (if w
                then
                  (let uu____4010 =
                     let uu____4015 =
                       let uu____4016 = FStar_Syntax_Print.term_to_string t in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4016 in
                     (FStar_Errors.Warning_NotEmbedded, uu____4015) in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____4010)
                else ();
                FStar_Pervasives_Native.None)) in
    mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq []
let (e_lid : FStar_Ident.lid FStar_Syntax_Embeddings.embedding) =
  let embed1 rng lid =
    let uu____4039 = FStar_Ident.path_of_lid lid in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____4039 in
  let unembed w t =
    let uu____4063 = unembed' w FStar_Syntax_Embeddings.e_string_list t in
    FStar_Util.map_opt uu____4063
      (fun p -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos) in
  let uu____4076 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x -> fun r -> fun uu____4083 -> fun uu____4084 -> embed1 r x)
    (fun x -> fun w -> fun uu____4091 -> unembed w x) uu____4076
    FStar_Ident.string_of_lid FStar_Syntax_Syntax.ET_abstract
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____4106 =
      let uu____4107 =
        let uu____4116 =
          embed FStar_Syntax_Embeddings.e_string rng
            bvv.FStar_Reflection_Data.bv_ppname in
        FStar_Syntax_Syntax.as_arg uu____4116 in
      let uu____4117 =
        let uu____4128 =
          let uu____4137 =
            embed FStar_Syntax_Embeddings.e_int rng
              bvv.FStar_Reflection_Data.bv_index in
          FStar_Syntax_Syntax.as_arg uu____4137 in
        let uu____4138 =
          let uu____4149 =
            let uu____4158 =
              embed e_term rng bvv.FStar_Reflection_Data.bv_sort in
            FStar_Syntax_Syntax.as_arg uu____4158 in
          [uu____4149] in
        uu____4128 :: uu____4138 in
      uu____4107 :: uu____4117 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4106 rng in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____4207 = FStar_Syntax_Util.head_and_args t1 in
    match uu____4207 with
    | (hd, args) ->
        let uu____4252 =
          let uu____4265 =
            let uu____4266 = FStar_Syntax_Util.un_uinst hd in
            uu____4266.FStar_Syntax_Syntax.n in
          (uu____4265, args) in
        (match uu____4252 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (nm, uu____4281)::(idx, uu____4283)::(s, uu____4285)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4330 = unembed' w FStar_Syntax_Embeddings.e_string nm in
             FStar_Util.bind_opt uu____4330
               (fun nm1 ->
                  let uu____4336 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx in
                  FStar_Util.bind_opt uu____4336
                    (fun idx1 ->
                       let uu____4342 = unembed' w e_term s in
                       FStar_Util.bind_opt uu____4342
                         (fun s1 ->
                            FStar_All.pipe_left
                              (fun uu____4349 ->
                                 FStar_Pervasives_Native.Some uu____4349)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4350 ->
             (if w
              then
                (let uu____4364 =
                   let uu____4369 =
                     let uu____4370 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4370 in
                   (FStar_Errors.Warning_NotEmbedded, uu____4369) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4364)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding) =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t, md) ->
        let uu____4391 =
          let uu____4392 =
            let uu____4401 = embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu____4401 in
          let uu____4402 =
            let uu____4413 =
              let uu____4422 =
                let uu____4423 = FStar_Syntax_Embeddings.e_option e_term in
                embed uu____4423 rng md in
              FStar_Syntax_Syntax.as_arg uu____4422 in
            [uu____4413] in
          uu____4392 :: uu____4402 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
          uu____4391 rng
    | FStar_Reflection_Data.C_GTotal (t, md) ->
        let uu____4460 =
          let uu____4461 =
            let uu____4470 = embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu____4470 in
          let uu____4471 =
            let uu____4482 =
              let uu____4491 =
                let uu____4492 = FStar_Syntax_Embeddings.e_option e_term in
                embed uu____4492 rng md in
              FStar_Syntax_Syntax.as_arg uu____4491 in
            [uu____4482] in
          uu____4461 :: uu____4471 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.t
          uu____4460 rng
    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
        let uu____4526 =
          let uu____4527 =
            let uu____4536 = embed e_term rng pre in
            FStar_Syntax_Syntax.as_arg uu____4536 in
          let uu____4537 =
            let uu____4548 =
              let uu____4557 = embed e_term rng post in
              FStar_Syntax_Syntax.as_arg uu____4557 in
            let uu____4558 =
              let uu____4569 =
                let uu____4578 = embed e_term rng pats in
                FStar_Syntax_Syntax.as_arg uu____4578 in
              [uu____4569] in
            uu____4548 :: uu____4558 in
          uu____4527 :: uu____4537 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
          uu____4526 rng
    | FStar_Reflection_Data.C_Eff (us, eff, res, args) ->
        let uu____4623 =
          let uu____4624 =
            let uu____4633 = embed FStar_Syntax_Embeddings.e_unit rng () in
            FStar_Syntax_Syntax.as_arg uu____4633 in
          let uu____4634 =
            let uu____4645 =
              let uu____4654 =
                embed FStar_Syntax_Embeddings.e_string_list rng eff in
              FStar_Syntax_Syntax.as_arg uu____4654 in
            let uu____4657 =
              let uu____4668 =
                let uu____4677 = embed e_term rng res in
                FStar_Syntax_Syntax.as_arg uu____4677 in
              let uu____4678 =
                let uu____4689 =
                  let uu____4698 =
                    let uu____4699 = FStar_Syntax_Embeddings.e_list e_argv in
                    embed uu____4699 rng args in
                  FStar_Syntax_Syntax.as_arg uu____4698 in
                [uu____4689] in
              uu____4668 :: uu____4678 in
            uu____4645 :: uu____4657 in
          uu____4624 :: uu____4634 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.t uu____4623
          rng in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____4762 = FStar_Syntax_Util.head_and_args t1 in
    match uu____4762 with
    | (hd, args) ->
        let uu____4807 =
          let uu____4820 =
            let uu____4821 = FStar_Syntax_Util.un_uinst hd in
            uu____4821.FStar_Syntax_Syntax.n in
          (uu____4820, args) in
        (match uu____4807 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (t2, uu____4836)::(md, uu____4838)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4873 = unembed' w e_term t2 in
             FStar_Util.bind_opt uu____4873
               (fun t3 ->
                  let uu____4879 =
                    let uu____4884 = FStar_Syntax_Embeddings.e_option e_term in
                    unembed' w uu____4884 md in
                  FStar_Util.bind_opt uu____4879
                    (fun md1 ->
                       FStar_All.pipe_left
                         (fun uu____4899 ->
                            FStar_Pervasives_Native.Some uu____4899)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (t2, uu____4904)::(md, uu____4906)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
             ->
             let uu____4941 = unembed' w e_term t2 in
             FStar_Util.bind_opt uu____4941
               (fun t3 ->
                  let uu____4947 =
                    let uu____4952 = FStar_Syntax_Embeddings.e_option e_term in
                    unembed' w uu____4952 md in
                  FStar_Util.bind_opt uu____4947
                    (fun md1 ->
                       FStar_All.pipe_left
                         (fun uu____4967 ->
                            FStar_Pervasives_Native.Some uu____4967)
                         (FStar_Reflection_Data.C_GTotal (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (pre, uu____4972)::(post, uu____4974)::(pats, uu____4976)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____5021 = unembed' w e_term pre in
             FStar_Util.bind_opt uu____5021
               (fun pre1 ->
                  let uu____5027 = unembed' w e_term post in
                  FStar_Util.bind_opt uu____5027
                    (fun post1 ->
                       let uu____5033 = unembed' w e_term pats in
                       FStar_Util.bind_opt uu____5033
                         (fun pats1 ->
                            FStar_All.pipe_left
                              (fun uu____5040 ->
                                 FStar_Pervasives_Native.Some uu____5040)
                              (FStar_Reflection_Data.C_Lemma
                                 (pre1, post1, pats1)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (us, uu____5043)::(eff, uu____5045)::(res, uu____5047)::(args1,
                                                                    uu____5049)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
             ->
             let uu____5104 = unembed' w FStar_Syntax_Embeddings.e_unit us in
             FStar_Util.bind_opt uu____5104
               (fun us1 ->
                  let uu____5110 =
                    unembed' w FStar_Syntax_Embeddings.e_string_list eff in
                  FStar_Util.bind_opt uu____5110
                    (fun eff1 ->
                       let uu____5124 = unembed' w e_term res in
                       FStar_Util.bind_opt uu____5124
                         (fun res1 ->
                            let uu____5130 =
                              let uu____5135 =
                                FStar_Syntax_Embeddings.e_list e_argv in
                              unembed' w uu____5135 args1 in
                            FStar_Util.bind_opt uu____5130
                              (fun args2 ->
                                 FStar_All.pipe_left
                                   (fun uu____5150 ->
                                      FStar_Pervasives_Native.Some uu____5150)
                                   (FStar_Reflection_Data.C_Eff
                                      ([], eff1, res1, args2))))))
         | uu____5155 ->
             (if w
              then
                (let uu____5169 =
                   let uu____5174 =
                     let uu____5175 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____5175 in
                   (FStar_Errors.Warning_NotEmbedded, uu____5174) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5169)
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
    let uu___722_5195 = r in
    {
      FStar_Syntax_Syntax.n = (uu___722_5195.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___722_5195.FStar_Syntax_Syntax.vars)
    } in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____5214 = FStar_Syntax_Util.head_and_args t1 in
    match uu____5214 with
    | (hd, args) ->
        let uu____5259 =
          let uu____5274 =
            let uu____5275 = FStar_Syntax_Util.un_uinst hd in
            uu____5275.FStar_Syntax_Syntax.n in
          (uu____5274, args) in
        (match uu____5259 with
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
         | uu____5347 ->
             (if w
              then
                (let uu____5363 =
                   let uu____5368 =
                     let uu____5369 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____5369 in
                   (FStar_Errors.Warning_NotEmbedded, uu____5368) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5363)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_order unembed_order FStar_Syntax_Syntax.t_order
let (e_sigelt : FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings.embedding)
  =
  let embed_sigelt rng se =
    FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng) in
  let unembed_sigelt w t =
    let uu____5399 =
      let uu____5400 = FStar_Syntax_Subst.compress t in
      uu____5400.FStar_Syntax_Syntax.n in
    match uu____5399 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt;
          FStar_Syntax_Syntax.ltyp = uu____5406;
          FStar_Syntax_Syntax.rng = uu____5407;_}
        ->
        let uu____5410 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____5410
    | uu____5411 ->
        (if w
         then
           (let uu____5413 =
              let uu____5418 =
                let uu____5419 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5419 in
              (FStar_Errors.Warning_NotEmbedded, uu____5418) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5413)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_string
      FStar_Syntax_Embeddings.e_range in
  FStar_Syntax_Embeddings.embed_as repr FStar_Ident.mk_ident
    (fun i ->
       let uu____5440 = FStar_Ident.string_of_id i in
       let uu____5441 = FStar_Ident.range_of_id i in (uu____5440, uu____5441))
    (FStar_Pervasives_Native.Some FStar_Reflection_Data.fstar_refl_ident)
let (e_univ_name :
  FStar_Syntax_Syntax.univ_name FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.set_type FStar_Reflection_Data.fstar_refl_univ_name
    e_ident
let (e_univ_names :
  FStar_Syntax_Syntax.univ_name Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_univ_name
let (e_ctor :
  (Prims.string Prims.list * FStar_Syntax_Syntax.term)
    FStar_Syntax_Embeddings.embedding)
  =
  FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_string_list
    e_term
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r, fv, univs, ty, t) ->
        let uu____5480 =
          let uu____5481 =
            let uu____5490 = embed FStar_Syntax_Embeddings.e_bool rng r in
            FStar_Syntax_Syntax.as_arg uu____5490 in
          let uu____5491 =
            let uu____5502 =
              let uu____5511 = embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu____5511 in
            let uu____5512 =
              let uu____5523 =
                let uu____5532 = embed e_univ_names rng univs in
                FStar_Syntax_Syntax.as_arg uu____5532 in
              let uu____5535 =
                let uu____5546 =
                  let uu____5555 = embed e_term rng ty in
                  FStar_Syntax_Syntax.as_arg uu____5555 in
                let uu____5556 =
                  let uu____5567 =
                    let uu____5576 = embed e_term rng t in
                    FStar_Syntax_Syntax.as_arg uu____5576 in
                  [uu____5567] in
                uu____5546 :: uu____5556 in
              uu____5523 :: uu____5535 in
            uu____5502 :: uu____5512 in
          uu____5481 :: uu____5491 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t uu____5480
          rng
    | FStar_Reflection_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu____5642 =
          let uu____5643 =
            let uu____5652 =
              embed FStar_Syntax_Embeddings.e_string_list rng nm in
            FStar_Syntax_Syntax.as_arg uu____5652 in
          let uu____5655 =
            let uu____5666 =
              let uu____5675 = embed e_univ_names rng univs in
              FStar_Syntax_Syntax.as_arg uu____5675 in
            let uu____5678 =
              let uu____5689 =
                let uu____5698 = embed e_binders rng bs in
                FStar_Syntax_Syntax.as_arg uu____5698 in
              let uu____5699 =
                let uu____5710 =
                  let uu____5719 = embed e_term rng t in
                  FStar_Syntax_Syntax.as_arg uu____5719 in
                let uu____5720 =
                  let uu____5731 =
                    let uu____5740 =
                      let uu____5741 = FStar_Syntax_Embeddings.e_list e_ctor in
                      embed uu____5741 rng dcs in
                    FStar_Syntax_Syntax.as_arg uu____5740 in
                  [uu____5731] in
                uu____5710 :: uu____5720 in
              uu____5689 :: uu____5699 in
            uu____5666 :: uu____5678 in
          uu____5643 :: uu____5655 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
          uu____5642 rng
    | FStar_Reflection_Data.Unk ->
        let uu___781_5814 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t in
        {
          FStar_Syntax_Syntax.n = (uu___781_5814.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___781_5814.FStar_Syntax_Syntax.vars)
        } in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____5831 = FStar_Syntax_Util.head_and_args t1 in
    match uu____5831 with
    | (hd, args) ->
        let uu____5876 =
          let uu____5889 =
            let uu____5890 = FStar_Syntax_Util.un_uinst hd in
            uu____5890.FStar_Syntax_Syntax.n in
          (uu____5889, args) in
        (match uu____5876 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (nm, uu____5905)::(us, uu____5907)::(bs, uu____5909)::(t2,
                                                                   uu____5911)::
            (dcs, uu____5913)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5978 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm in
             FStar_Util.bind_opt uu____5978
               (fun nm1 ->
                  let uu____5992 = unembed' w e_univ_names us in
                  FStar_Util.bind_opt uu____5992
                    (fun us1 ->
                       let uu____6006 = unembed' w e_binders bs in
                       FStar_Util.bind_opt uu____6006
                         (fun bs1 ->
                            let uu____6012 = unembed' w e_term t2 in
                            FStar_Util.bind_opt uu____6012
                              (fun t3 ->
                                 let uu____6018 =
                                   let uu____6029 =
                                     FStar_Syntax_Embeddings.e_list e_ctor in
                                   unembed' w uu____6029 dcs in
                                 FStar_Util.bind_opt uu____6018
                                   (fun dcs1 ->
                                      FStar_All.pipe_left
                                        (fun uu____6074 ->
                                           FStar_Pervasives_Native.Some
                                             uu____6074)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (r, uu____6083)::(fvar, uu____6085)::(univs, uu____6087)::
            (ty, uu____6089)::(t2, uu____6091)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____6156 = unembed' w FStar_Syntax_Embeddings.e_bool r in
             FStar_Util.bind_opt uu____6156
               (fun r1 ->
                  let uu____6162 = unembed' w e_fv fvar in
                  FStar_Util.bind_opt uu____6162
                    (fun fvar1 ->
                       let uu____6168 = unembed' w e_univ_names univs in
                       FStar_Util.bind_opt uu____6168
                         (fun univs1 ->
                            let uu____6182 = unembed' w e_term ty in
                            FStar_Util.bind_opt uu____6182
                              (fun ty1 ->
                                 let uu____6188 = unembed' w e_term t2 in
                                 FStar_Util.bind_opt uu____6188
                                   (fun t3 ->
                                      FStar_All.pipe_left
                                        (fun uu____6195 ->
                                           FStar_Pervasives_Native.Some
                                             uu____6195)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar1, univs1, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6213 ->
             (if w
              then
                (let uu____6227 =
                   let uu____6232 =
                     let uu____6233 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6233 in
                   (FStar_Errors.Warning_NotEmbedded, uu____6232) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6227)
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
          let uu____6254 =
            let uu____6255 =
              let uu____6264 =
                let uu____6265 = FStar_BigInt.string_of_big_int i in
                FStar_Syntax_Util.exp_int uu____6265 in
              FStar_Syntax_Syntax.as_arg uu____6264 in
            [uu____6255] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
            uu____6254 FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1, e2) ->
          let uu____6284 =
            let uu____6285 =
              let uu____6294 = embed_exp rng e1 in
              FStar_Syntax_Syntax.as_arg uu____6294 in
            let uu____6295 =
              let uu____6306 =
                let uu____6315 = embed_exp rng e2 in
                FStar_Syntax_Syntax.as_arg uu____6315 in
              [uu____6306] in
            uu____6285 :: uu____6295 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
            uu____6284 FStar_Range.dummyRange in
    let uu___856_6340 = r in
    {
      FStar_Syntax_Syntax.n = (uu___856_6340.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___856_6340.FStar_Syntax_Syntax.vars)
    } in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____6359 = FStar_Syntax_Util.head_and_args t1 in
    match uu____6359 with
    | (hd, args) ->
        let uu____6404 =
          let uu____6417 =
            let uu____6418 = FStar_Syntax_Util.un_uinst hd in
            uu____6418.FStar_Syntax_Syntax.n in
          (uu____6417, args) in
        (match uu____6404 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv, (i, uu____6448)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6473 = unembed' w FStar_Syntax_Embeddings.e_int i in
             FStar_Util.bind_opt uu____6473
               (fun i1 ->
                  FStar_All.pipe_left
                    (fun uu____6480 ->
                       FStar_Pervasives_Native.Some uu____6480)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (e1, uu____6483)::(e2, uu____6485)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6520 = unembed_exp w e1 in
             FStar_Util.bind_opt uu____6520
               (fun e11 ->
                  let uu____6526 = unembed_exp w e2 in
                  FStar_Util.bind_opt uu____6526
                    (fun e21 ->
                       FStar_All.pipe_left
                         (fun uu____6533 ->
                            FStar_Pervasives_Native.Some uu____6533)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6534 ->
             (if w
              then
                (let uu____6548 =
                   let uu____6553 =
                     let uu____6554 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6554 in
                   (FStar_Errors.Warning_NotEmbedded, uu____6553) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6548)
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
          let uu____6583 =
            let uu____6584 =
              let uu____6593 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu____6593 in
            [uu____6584] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
            uu____6583 FStar_Range.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu____6611 =
            let uu____6612 =
              let uu____6621 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu____6621 in
            [uu____6612] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
            uu____6611 FStar_Range.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu____6639 =
            let uu____6640 =
              let uu____6649 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu____6649 in
            [uu____6640] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
            uu____6639 FStar_Range.dummyRange
      | FStar_Reflection_Data.Projector (l, i) ->
          let uu____6668 =
            let uu____6669 =
              let uu____6678 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu____6678 in
            let uu____6679 =
              let uu____6690 =
                let uu____6699 = embed e_ident rng i in
                FStar_Syntax_Syntax.as_arg uu____6699 in
              [uu____6690] in
            uu____6669 :: uu____6679 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
            uu____6668 FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordType (ids1, ids2) ->
          let uu____6734 =
            let uu____6735 =
              let uu____6744 =
                let uu____6745 = FStar_Syntax_Embeddings.e_list e_ident in
                embed uu____6745 rng ids1 in
              FStar_Syntax_Syntax.as_arg uu____6744 in
            let uu____6752 =
              let uu____6763 =
                let uu____6772 =
                  let uu____6773 = FStar_Syntax_Embeddings.e_list e_ident in
                  embed uu____6773 rng ids2 in
                FStar_Syntax_Syntax.as_arg uu____6772 in
              [uu____6763] in
            uu____6735 :: uu____6752 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
            uu____6734 FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1, ids2) ->
          let uu____6814 =
            let uu____6815 =
              let uu____6824 =
                let uu____6825 = FStar_Syntax_Embeddings.e_list e_ident in
                embed uu____6825 rng ids1 in
              FStar_Syntax_Syntax.as_arg uu____6824 in
            let uu____6832 =
              let uu____6843 =
                let uu____6852 =
                  let uu____6853 = FStar_Syntax_Embeddings.e_list e_ident in
                  embed uu____6853 rng ids2 in
                FStar_Syntax_Syntax.as_arg uu____6852 in
              [uu____6843] in
            uu____6815 :: uu____6832 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
            uu____6814 FStar_Range.dummyRange in
    let uu___931_6884 = r in
    {
      FStar_Syntax_Syntax.n = (uu___931_6884.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___931_6884.FStar_Syntax_Syntax.vars)
    } in
  let unembed w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____6903 = FStar_Syntax_Util.head_and_args t1 in
    match uu____6903 with
    | (hd, args) ->
        let uu____6948 =
          let uu____6961 =
            let uu____6962 = FStar_Syntax_Util.un_uinst hd in
            uu____6962.FStar_Syntax_Syntax.n in
          (uu____6961, args) in
        (match uu____6948 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____7232)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7257 = unembed' w e_lid l in
             FStar_Util.bind_opt uu____7257
               (fun l1 ->
                  FStar_All.pipe_left
                    (fun uu____7264 ->
                       FStar_Pervasives_Native.Some uu____7264)
                    (FStar_Reflection_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____7267)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7292 = unembed' w e_lid l in
             FStar_Util.bind_opt uu____7292
               (fun l1 ->
                  FStar_All.pipe_left
                    (fun uu____7299 ->
                       FStar_Pervasives_Native.Some uu____7299)
                    (FStar_Reflection_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu____7302)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7327 = unembed' w e_lid l in
             FStar_Util.bind_opt uu____7327
               (fun l1 ->
                  FStar_All.pipe_left
                    (fun uu____7334 ->
                       FStar_Pervasives_Native.Some uu____7334)
                    (FStar_Reflection_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (l, uu____7337)::(i, uu____7339)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7374 = unembed' w e_lid l in
             FStar_Util.bind_opt uu____7374
               (fun l1 ->
                  let uu____7380 = unembed' w e_ident i in
                  FStar_Util.bind_opt uu____7380
                    (fun i1 ->
                       FStar_All.pipe_left
                         (fun uu____7387 ->
                            FStar_Pervasives_Native.Some uu____7387)
                         (FStar_Reflection_Data.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (ids1, uu____7390)::(ids2, uu____7392)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7427 =
               let uu____7432 = FStar_Syntax_Embeddings.e_list e_ident in
               unembed' w uu____7432 ids1 in
             FStar_Util.bind_opt uu____7427
               (fun ids11 ->
                  let uu____7446 =
                    let uu____7451 = FStar_Syntax_Embeddings.e_list e_ident in
                    unembed' w uu____7451 ids2 in
                  FStar_Util.bind_opt uu____7446
                    (fun ids21 ->
                       FStar_All.pipe_left
                         (fun uu____7466 ->
                            FStar_Pervasives_Native.Some uu____7466)
                         (FStar_Reflection_Data.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (ids1, uu____7473)::(ids2, uu____7475)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____7510 =
               let uu____7515 = FStar_Syntax_Embeddings.e_list e_ident in
               unembed' w uu____7515 ids1 in
             FStar_Util.bind_opt uu____7510
               (fun ids11 ->
                  let uu____7529 =
                    let uu____7534 = FStar_Syntax_Embeddings.e_list e_ident in
                    unembed' w uu____7534 ids2 in
                  FStar_Util.bind_opt uu____7529
                    (fun ids21 ->
                       FStar_All.pipe_left
                         (fun uu____7549 ->
                            FStar_Pervasives_Native.Some uu____7549)
                         (FStar_Reflection_Data.RecordConstructor
                            (ids11, ids21))))
         | uu____7554 ->
             (if w
              then
                (let uu____7568 =
                   let uu____7573 =
                     let uu____7574 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____7574 in
                   (FStar_Errors.Warning_NotEmbedded, uu____7573) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7568)
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
    let uu____7586 =
      let uu____7587 =
        let uu____7596 =
          let uu____7597 = FStar_Reflection_Basic.inspect_bv bv in
          embed e_bv_view i.FStar_Syntax_Syntax.rng uu____7597 in
        FStar_Syntax_Syntax.as_arg uu____7596 in
      [uu____7587] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
      uu____7586 i.FStar_Syntax_Syntax.rng
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu____7620 = FStar_Reflection_Basic.inspect_binder binder in
    match uu____7620 with
    | (bv, aq) ->
        let uu____7627 =
          let uu____7628 =
            let uu____7637 = embed e_bv i.FStar_Syntax_Syntax.rng bv in
            FStar_Syntax_Syntax.as_arg uu____7637 in
          let uu____7638 =
            let uu____7649 =
              let uu____7658 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq in
              FStar_Syntax_Syntax.as_arg uu____7658 in
            [uu____7649] in
          uu____7628 :: uu____7638 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
          uu____7627 i.FStar_Syntax_Syntax.rng
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu____7689 =
      let uu____7690 =
        let uu____7699 =
          let uu____7700 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string in
          let uu____7705 = FStar_Reflection_Basic.inspect_fv fv in
          embed uu____7700 i.FStar_Syntax_Syntax.rng uu____7705 in
        FStar_Syntax_Syntax.as_arg uu____7699 in
      [uu____7690] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
      uu____7689 i.FStar_Syntax_Syntax.rng
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu____7732 =
      let uu____7733 =
        let uu____7742 =
          let uu____7743 = FStar_Reflection_Basic.inspect_comp comp in
          embed e_comp_view i.FStar_Syntax_Syntax.rng uu____7743 in
        FStar_Syntax_Syntax.as_arg uu____7742 in
      [uu____7733] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
      uu____7732 i.FStar_Syntax_Syntax.rng
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
    let uu____7776 =
      let uu____7777 =
        let uu____7786 =
          let uu____7787 = FStar_Reflection_Basic.inspect_sigelt sigelt in
          embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____7787 in
        FStar_Syntax_Syntax.as_arg uu____7786 in
      [uu____7777] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
      uu____7776 i.FStar_Syntax_Syntax.rng