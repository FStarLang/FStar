open Prims
let (noaqs : FStar_Syntax_Syntax.antiquotations) = (Prims.int_zero, [])
let mk_emb :
  'uuuuu .
    (FStar_Compiler_Range.range -> 'uuuuu -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'uuuuu FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term -> 'uuuuu FStar_Syntax_Embeddings.embedding
  =
  fun f ->
    fun g ->
      fun t ->
        let uu___ = FStar_Syntax_Embeddings.term_as_fv t in
        FStar_Syntax_Embeddings.mk_emb
          (fun x -> fun r -> fun _topt -> fun _norm -> f r x)
          (fun x -> fun w -> fun _norm -> g w x) uu___
let embed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings.embedding ->
      FStar_Compiler_Range.range -> 'uuuuu -> FStar_Syntax_Syntax.term
  =
  fun e ->
    fun r ->
      fun x ->
        let uu___ = FStar_Syntax_Embeddings.embed e x in
        uu___ r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
let unembed' :
  'uuuuu .
    Prims.bool ->
      'uuuuu FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term -> 'uuuuu FStar_Pervasives_Native.option
  =
  fun w ->
    fun e ->
      fun x ->
        let uu___ = FStar_Syntax_Embeddings.unembed e x in
        uu___ w FStar_Syntax_Embeddings.id_norm_cb
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Constants.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng) in
  let unembed_bv w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.format1 "Not an embedded bv: %s" uu___5 in
              (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_bv unembed_bv FStar_Reflection_Constants.fstar_refl_bv
let (e_binder : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding)
  =
  let embed_binder rng b =
    FStar_Syntax_Util.mk_lazy b FStar_Reflection_Constants.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng) in
  let unembed_binder w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.format1 "Not an embedded binder: %s"
                  uu___5 in
              (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_binder unembed_binder
    FStar_Reflection_Constants.fstar_refl_binder
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
          let uu___ = f x in
          FStar_Compiler_Util.bind_opt uu___
            (fun x1 ->
               let uu___1 = mapM_opt f xs in
               FStar_Compiler_Util.bind_opt uu___1
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
          FStar_Syntax_Syntax.antiquotations = aq
        } in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (t, qi)) rng in
    let rec unembed_term w t =
      let apply_antiquotations t1 aq1 =
        let uu___ = aq1 in
        match uu___ with
        | (shift, aqs) ->
            let aqs1 = FStar_Compiler_List.rev aqs in
            let uu___1 = mapM_opt (unembed_term w) aqs1 in
            FStar_Compiler_Util.bind_opt uu___1
              (fun aq_ts ->
                 let uu___2 =
                   let uu___3 =
                     FStar_Compiler_Effect.op_Bar_Greater aq_ts
                       (FStar_Compiler_List.mapi
                          (fun i ->
                             fun at ->
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None
                                   FStar_Syntax_Syntax.t_term in
                               ((FStar_Syntax_Syntax.DB ((shift + i), x)),
                                 (FStar_Syntax_Syntax.NT (x, at))))) in
                   FStar_Compiler_Effect.op_Bar_Greater uu___3
                     FStar_Compiler_List.unzip in
                 match uu___2 with
                 | (subst_open, subst) ->
                     let uu___3 =
                       let uu___4 = FStar_Syntax_Subst.subst subst_open t1 in
                       FStar_Compiler_Effect.op_Less_Bar
                         (FStar_Syntax_Subst.subst subst) uu___4 in
                     FStar_Pervasives_Native.Some uu___3) in
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress t1 in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          let r =
            apply_antiquotations tm qi.FStar_Syntax_Syntax.antiquotations in
          ((match r with
            | FStar_Pervasives_Native.None when w ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Compiler_Util.format1
                      "Failed to unembed antiquotations for: %s" uu___4 in
                  (FStar_Errors_Codes.Warning_NotEmbedded, uu___3) in
                FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___2
            | uu___2 -> ());
           r)
      | uu___1 ->
          (if w
           then
             (let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Compiler_Util.format1 "Not an embedded term: %s"
                    uu___5 in
                (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___3)
           else ();
           FStar_Pervasives_Native.None) in
    mk_emb embed_term unembed_term FStar_Syntax_Syntax.t_term
let (e_term : FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding) =
  e_term_aq noaqs
let (e_aqualv :
  FStar_Reflection_Data.aqualv FStar_Syntax_Embeddings.embedding) =
  let embed_aqualv rng q =
    let r =
      match q with
      | FStar_Reflection_Data.Q_Explicit ->
          FStar_Reflection_Constants.ref_Q_Explicit.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Q_Implicit ->
          FStar_Reflection_Constants.ref_Q_Implicit.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Q_Meta t ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_term rng t in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Q_Meta.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Q_Explicit.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Q_Implicit.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Q_Meta.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w e_term t2 in
             FStar_Compiler_Util.bind_opt uu___3
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1 "Not an embedded aqualv: %s"
                       uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_aqualv unembed_aqualv
    FStar_Reflection_Constants.fstar_refl_aqualv
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_list e_binder
let (e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings.embedding) =
  let embed_fv rng fv =
    FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Constants.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng) in
  let unembed_fv w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.format1 "Not an embedded fvar: %s" uu___5 in
              (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_fv unembed_fv FStar_Reflection_Constants.fstar_refl_fv
let (e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding) =
  let embed_comp rng c =
    FStar_Syntax_Util.mk_lazy c FStar_Reflection_Constants.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng) in
  let unembed_comp w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.format1 "Not an embedded comp: %s" uu___5 in
              (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_comp unembed_comp FStar_Reflection_Constants.fstar_refl_comp
let (e_universe :
  FStar_Syntax_Syntax.universe FStar_Syntax_Embeddings.embedding) =
  let embed_universe rng u =
    FStar_Syntax_Util.mk_lazy u
      FStar_Reflection_Constants.fstar_refl_universe
      FStar_Syntax_Syntax.Lazy_universe (FStar_Pervasives_Native.Some rng) in
  let unembed_universe w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_universe;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.format1 "Not an embedded universe: %s"
                  uu___5 in
              (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_universe unembed_universe
    FStar_Reflection_Constants.fstar_refl_universe
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_string
      FStar_Syntax_Embeddings.e_range in
  FStar_Syntax_Embeddings.embed_as repr FStar_Ident.mk_ident
    (fun i ->
       let uu___ = FStar_Ident.string_of_id i in
       let uu___1 = FStar_Ident.range_of_id i in (uu___, uu___1))
    (FStar_Pervasives_Native.Some FStar_Reflection_Constants.fstar_refl_ident)
let (e_universe_view :
  FStar_Reflection_Data.universe_view FStar_Syntax_Embeddings.embedding) =
  let embed_universe_view rng uv =
    match uv with
    | FStar_Reflection_Data.Uv_Zero ->
        FStar_Reflection_Constants.ref_Uv_Zero.FStar_Reflection_Constants.t
    | FStar_Reflection_Data.Uv_Succ u ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_universe rng u in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Uv_Succ.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Uv_Max us ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Embeddings.e_list e_universe in
              embed uu___3 rng us in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Uv_Max.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Uv_BVar n ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStar_Syntax_Embeddings.e_int rng n in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Uv_BVar.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Uv_Name i ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Syntax_Embeddings.e_tuple2
                  FStar_Syntax_Embeddings.e_string
                  FStar_Syntax_Embeddings.e_range in
              embed uu___3 rng i in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Uv_Name.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Uv_Unif u ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Syntax_Util.mk_lazy u FStar_Syntax_Util.t_universe_uvar
                FStar_Syntax_Syntax.Lazy_universe_uvar
                FStar_Pervasives_Native.None in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Uv_Unif.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Uv_Unk ->
        FStar_Reflection_Constants.ref_Uv_Unk.FStar_Reflection_Constants.t in
  let unembed_universe_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Uv_Zero.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Uv_Zero
         | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Uv_Succ.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w e_universe u in
             FStar_Compiler_Util.bind_opt uu___3
               (fun u1 ->
                  let uu___4 =
                    FStar_Compiler_Effect.op_Bar_Greater u1
                      (fun uu___5 -> FStar_Reflection_Data.Uv_Succ uu___5) in
                  FStar_Compiler_Effect.op_Bar_Greater uu___4
                    (fun uu___5 -> FStar_Pervasives_Native.Some uu___5))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (us, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Uv_Max.FStar_Reflection_Constants.lid
             ->
             let uu___3 =
               let uu___4 = FStar_Syntax_Embeddings.e_list e_universe in
               unembed' w uu___4 us in
             FStar_Compiler_Util.bind_opt uu___3
               (fun us1 ->
                  let uu___4 =
                    FStar_Compiler_Effect.op_Bar_Greater us1
                      (fun uu___5 -> FStar_Reflection_Data.Uv_Max uu___5) in
                  FStar_Compiler_Effect.op_Bar_Greater uu___4
                    (fun uu___5 -> FStar_Pervasives_Native.Some uu___5))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (n, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Uv_BVar.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w FStar_Syntax_Embeddings.e_int n in
             FStar_Compiler_Util.bind_opt uu___3
               (fun n1 ->
                  let uu___4 =
                    FStar_Compiler_Effect.op_Bar_Greater n1
                      (fun uu___5 -> FStar_Reflection_Data.Uv_BVar uu___5) in
                  FStar_Compiler_Effect.op_Bar_Greater uu___4
                    (fun uu___5 -> FStar_Pervasives_Native.Some uu___5))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (i, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Uv_Name.FStar_Reflection_Constants.lid
             ->
             let uu___3 =
               let uu___4 =
                 FStar_Syntax_Embeddings.e_tuple2
                   FStar_Syntax_Embeddings.e_string
                   FStar_Syntax_Embeddings.e_range in
               unembed' w uu___4 i in
             FStar_Compiler_Util.bind_opt uu___3
               (fun i1 ->
                  let uu___4 =
                    FStar_Compiler_Effect.op_Bar_Greater i1
                      (fun uu___5 -> FStar_Reflection_Data.Uv_Name uu___5) in
                  FStar_Compiler_Effect.op_Bar_Greater uu___4
                    (fun uu___5 -> FStar_Pervasives_Native.Some uu___5))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Uv_Unif.FStar_Reflection_Constants.lid
             ->
             let u1 =
               FStar_Syntax_Util.unlazy_as_t
                 FStar_Syntax_Syntax.Lazy_universe_uvar u in
             let uu___3 =
               FStar_Compiler_Effect.op_Bar_Greater u1
                 (fun uu___4 -> FStar_Reflection_Data.Uv_Unif uu___4) in
             FStar_Compiler_Effect.op_Bar_Greater uu___3
               (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Uv_Unk.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Uv_Unk
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1
                       "Not an embedded universe view: %s" uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_universe_view unembed_universe_view
    FStar_Reflection_Constants.fstar_refl_universe_view
let (e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding) =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_Constants.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng) in
  let unembed_env w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.format1 "Not an embedded env: %s" uu___5 in
              (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_env unembed_env FStar_Reflection_Constants.fstar_refl_env
let (e_const :
  FStar_Reflection_Data.vconst FStar_Syntax_Embeddings.embedding) =
  let embed_const rng c =
    let r =
      match c with
      | FStar_Reflection_Data.C_Unit ->
          FStar_Reflection_Constants.ref_C_Unit.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.C_True ->
          FStar_Reflection_Constants.ref_C_True.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.C_False ->
          FStar_Reflection_Constants.ref_C_False.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.C_Int i ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_BigInt.string_of_big_int i in
                FStar_Syntax_Util.exp_int uu___3 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_C_Int.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_string rng s in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_C_String.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange
      | FStar_Reflection_Data.C_Range r1 ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_range rng r1 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_C_Range.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange
      | FStar_Reflection_Data.C_Reify ->
          FStar_Reflection_Constants.ref_C_Reify.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_string_list rng ns in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_C_Reflect.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_Unit.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_True.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_False.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv, (i, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_Int.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w FStar_Syntax_Embeddings.e_int i in
             FStar_Compiler_Util.bind_opt uu___3
               (fun i1 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (s, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_String.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w FStar_Syntax_Embeddings.e_string s in
             FStar_Compiler_Util.bind_opt uu___3
               (fun s1 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (r, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_Range.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w FStar_Syntax_Embeddings.e_range r in
             FStar_Compiler_Util.bind_opt uu___3
               (fun r1 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_Reify.FStar_Reflection_Constants.lid
             ->
             FStar_Compiler_Effect.op_Less_Bar
               (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv, (ns, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_Reflect.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w FStar_Syntax_Embeddings.e_string_list ns in
             FStar_Compiler_Util.bind_opt uu___3
               (fun ns1 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1 "Not an embedded vconst: %s"
                       uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_const unembed_const
    FStar_Reflection_Constants.fstar_refl_vconst
let rec e_pattern_aq :
  'uuuuu .
    'uuuuu -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding
  =
  fun aq ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Pat_Constant.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Pat_Cons (fv, us_opt, ps) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 = FStar_Syntax_Embeddings.e_list e_universe in
                    FStar_Syntax_Embeddings.e_option uu___6 in
                  embed uu___5 rng us_opt in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 = e_pattern_aq aq in
                        FStar_Syntax_Embeddings.e_tuple2 uu___9
                          FStar_Syntax_Embeddings.e_bool in
                      FStar_Syntax_Embeddings.e_list uu___8 in
                    embed uu___7 rng ps in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Pat_Cons.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Pat_Var.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Pat_Wild.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Pat_Dot_Term eopt ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Embeddings.e_option e_term in
                embed uu___3 rng eopt in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Pat_Dot_Term.FStar_Reflection_Constants.t
            uu___ rng in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t in
      let uu___ = FStar_Syntax_Util.head_and_args t1 in
      match uu___ with
      | (hd, args) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Util.un_uinst hd in
              uu___3.FStar_Syntax_Syntax.n in
            (uu___2, args) in
          (match uu___1 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (c, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Pat_Constant.FStar_Reflection_Constants.lid
               ->
               let uu___3 = unembed' w e_const c in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun c1 ->
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (f, uu___2)::(us_opt, uu___3)::(ps, uu___4)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Pat_Cons.FStar_Reflection_Constants.lid
               ->
               let uu___5 = unembed' w e_fv f in
               FStar_Compiler_Util.bind_opt uu___5
                 (fun f1 ->
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          FStar_Syntax_Embeddings.e_list e_universe in
                        FStar_Syntax_Embeddings.e_option uu___8 in
                      unembed' w uu___7 us_opt in
                    FStar_Compiler_Util.bind_opt uu___6
                      (fun us_opt1 ->
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               let uu___10 = e_pattern_aq aq in
                               FStar_Syntax_Embeddings.e_tuple2 uu___10
                                 FStar_Syntax_Embeddings.e_bool in
                             FStar_Syntax_Embeddings.e_list uu___9 in
                           unembed' w uu___8 ps in
                         FStar_Compiler_Util.bind_opt uu___7
                           (fun ps1 ->
                              FStar_Compiler_Effect.op_Less_Bar
                                (fun uu___8 ->
                                   FStar_Pervasives_Native.Some uu___8)
                                (FStar_Reflection_Data.Pat_Cons
                                   (f1, us_opt1, ps1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (bv, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Pat_Var.FStar_Reflection_Constants.lid
               ->
               let uu___3 = unembed' w e_bv bv in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun bv1 ->
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (bv, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Pat_Wild.FStar_Reflection_Constants.lid
               ->
               let uu___3 = unembed' w e_bv bv in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun bv1 ->
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (eopt, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Pat_Dot_Term.FStar_Reflection_Constants.lid
               ->
               let uu___3 =
                 let uu___4 = FStar_Syntax_Embeddings.e_option e_term in
                 unembed' w uu___4 eopt in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun eopt1 ->
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                      (FStar_Reflection_Data.Pat_Dot_Term eopt1))
           | uu___2 ->
               (if w
                then
                  (let uu___4 =
                     let uu___5 =
                       let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                       FStar_Compiler_Util.format1
                         "Not an embedded pattern: %s" uu___6 in
                     (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
                else ();
                FStar_Pervasives_Native.None)) in
    mk_emb embed_pattern unembed_pattern
      FStar_Reflection_Constants.fstar_refl_pattern
let (e_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  e_pattern_aq noaqs
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
    let uu___ = e_pattern_aq aq in
    let uu___1 = e_term_aq aq in
    FStar_Syntax_Embeddings.e_tuple2 uu___ uu___1
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq ->
    let uu___ = e_term_aq aq in
    FStar_Syntax_Embeddings.e_tuple2 uu___ e_aqualv
let (e_match_returns_annotation :
  (FStar_Syntax_Syntax.binder * ((FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.comp) FStar_Pervasives.either *
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool))
    FStar_Pervasives_Native.option FStar_Syntax_Embeddings.embedding)
  =
  let uu___ =
    let uu___1 =
      let uu___2 = FStar_Syntax_Embeddings.e_either e_term e_comp in
      let uu___3 = FStar_Syntax_Embeddings.e_option e_term in
      FStar_Syntax_Embeddings.e_tuple3 uu___2 uu___3
        FStar_Syntax_Embeddings.e_bool in
    FStar_Syntax_Embeddings.e_tuple2 e_binder uu___1 in
  FStar_Syntax_Embeddings.e_option uu___
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq ->
    let push uu___ =
      match uu___ with | (s, aq1) -> ((s + Prims.int_one), aq1) in
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_FVar.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_BVar.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Var.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_UInst (fv, us) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_Syntax_Embeddings.e_list e_universe in
                  embed uu___5 rng us in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_UInst.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_App (hd, a) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng hd in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = let uu___5 = e_argv_aq aq in embed uu___5 rng a in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_App.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Abs (b, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq (push aq) in embed uu___5 rng t1 in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Abs.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = embed e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Arrow.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_universe rng u in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Type.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Refine (bv, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq (push aq) in embed uu___5 rng t1 in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Refine.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Const.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Uvar (u, d) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_int rng u in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Syntax_Util.mk_lazy (u, d)
                    FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Uvar.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Let (r, attrs, b, t1, t2) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_bool rng r in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_Syntax_Embeddings.e_list e_term in
                  embed uu___5 rng attrs in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 = embed e_bv rng b in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      let uu___9 = e_term_aq aq in embed uu___9 rng t1 in
                    FStar_Syntax_Syntax.as_arg uu___8 in
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 = e_term_aq (push aq) in
                        embed uu___11 rng t2 in
                      FStar_Syntax_Syntax.as_arg uu___10 in
                    [uu___9] in
                  uu___7 :: uu___8 in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Let.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Match (t1, ret_opt, brs) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng t1 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = embed e_match_returns_annotation rng ret_opt in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_branch_aq aq in
                      FStar_Syntax_Embeddings.e_list uu___8 in
                    embed uu___7 rng brs in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Match.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_AscribedT (e, t1, tacopt, use_eq) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng e in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = let uu___5 = e_term_aq aq in embed uu___5 rng t1 in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu___8 in
                    embed uu___7 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      embed FStar_Syntax_Embeddings.e_bool rng use_eq in
                    FStar_Syntax_Syntax.as_arg uu___8 in
                  [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_AscT.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng e in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = embed e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu___8 in
                    embed uu___7 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      embed FStar_Syntax_Embeddings.e_bool rng use_eq in
                    FStar_Syntax_Syntax.as_arg uu___8 in
                  [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_AscC.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Unknown ->
          let uu___ =
            FStar_Reflection_Constants.ref_Tv_Unknown.FStar_Reflection_Constants.t in
          {
            FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars);
            FStar_Syntax_Syntax.hash_code =
              (uu___.FStar_Syntax_Syntax.hash_code)
          } in
    let unembed_term_view w t =
      let uu___ = FStar_Syntax_Util.head_and_args t in
      match uu___ with
      | (hd, args) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Util.un_uinst hd in
              uu___3.FStar_Syntax_Syntax.n in
            (uu___2, args) in
          (match uu___1 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Var.FStar_Reflection_Constants.lid
               ->
               let uu___3 = unembed' w e_bv b in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun b1 ->
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_BVar.FStar_Reflection_Constants.lid
               ->
               let uu___3 = unembed' w e_bv b in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun b1 ->
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (f, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_FVar.FStar_Reflection_Constants.lid
               ->
               let uu___3 = unembed' w e_fv f in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun f1 ->
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (f, uu___2)::(us, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_UInst.FStar_Reflection_Constants.lid
               ->
               let uu___4 = unembed' w e_fv f in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun f1 ->
                    let uu___5 =
                      let uu___6 = FStar_Syntax_Embeddings.e_list e_universe in
                      unembed' w uu___6 us in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun us1 ->
                         FStar_Compiler_Effect.op_Less_Bar
                           (fun uu___6 -> FStar_Pervasives_Native.Some uu___6)
                           (FStar_Reflection_Data.Tv_UInst (f1, us1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::(r, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_App.FStar_Reflection_Constants.lid
               ->
               let uu___4 = unembed' w e_term l in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun l1 ->
                    let uu___5 = unembed' w e_argv r in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun r1 ->
                         FStar_Compiler_Effect.op_Less_Bar
                           (fun uu___6 -> FStar_Pervasives_Native.Some uu___6)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::(t1, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Abs.FStar_Reflection_Constants.lid
               ->
               let uu___4 = unembed' w e_binder b in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun b1 ->
                    let uu___5 = unembed' w e_term t1 in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun t2 ->
                         FStar_Compiler_Effect.op_Less_Bar
                           (fun uu___6 -> FStar_Pervasives_Native.Some uu___6)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::(t1, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Arrow.FStar_Reflection_Constants.lid
               ->
               let uu___4 = unembed' w e_binder b in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun b1 ->
                    let uu___5 = unembed' w e_comp t1 in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun c ->
                         FStar_Compiler_Effect.op_Less_Bar
                           (fun uu___6 -> FStar_Pervasives_Native.Some uu___6)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Type.FStar_Reflection_Constants.lid
               ->
               let uu___3 = unembed' w e_universe u in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun u1 ->
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                      (FStar_Reflection_Data.Tv_Type u1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::(t1, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Refine.FStar_Reflection_Constants.lid
               ->
               let uu___4 = unembed' w e_bv b in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun b1 ->
                    let uu___5 = unembed' w e_term t1 in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun t2 ->
                         FStar_Compiler_Effect.op_Less_Bar
                           (fun uu___6 -> FStar_Pervasives_Native.Some uu___6)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (c, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Const.FStar_Reflection_Constants.lid
               ->
               let uu___3 = unembed' w e_const c in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun c1 ->
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::(l, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Uvar.FStar_Reflection_Constants.lid
               ->
               let uu___4 = unembed' w FStar_Syntax_Embeddings.e_int u in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun u1 ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l in
                    FStar_Compiler_Effect.op_Less_Bar
                      (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (r, uu___2)::(attrs, uu___3)::(b, uu___4)::(t1, uu___5)::
              (t2, uu___6)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Let.FStar_Reflection_Constants.lid
               ->
               let uu___7 = unembed' w FStar_Syntax_Embeddings.e_bool r in
               FStar_Compiler_Util.bind_opt uu___7
                 (fun r1 ->
                    let uu___8 =
                      let uu___9 = FStar_Syntax_Embeddings.e_list e_term in
                      unembed' w uu___9 attrs in
                    FStar_Compiler_Util.bind_opt uu___8
                      (fun attrs1 ->
                         let uu___9 = unembed' w e_bv b in
                         FStar_Compiler_Util.bind_opt uu___9
                           (fun b1 ->
                              let uu___10 = unembed' w e_term t1 in
                              FStar_Compiler_Util.bind_opt uu___10
                                (fun t11 ->
                                   let uu___11 = unembed' w e_term t2 in
                                   FStar_Compiler_Util.bind_opt uu___11
                                     (fun t21 ->
                                        FStar_Compiler_Effect.op_Less_Bar
                                          (fun uu___12 ->
                                             FStar_Pervasives_Native.Some
                                               uu___12)
                                          (FStar_Reflection_Data.Tv_Let
                                             (r1, attrs1, b1, t11, t21)))))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (t1, uu___2)::(ret_opt, uu___3)::(brs, uu___4)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Match.FStar_Reflection_Constants.lid
               ->
               let uu___5 = unembed' w e_term t1 in
               FStar_Compiler_Util.bind_opt uu___5
                 (fun t2 ->
                    let uu___6 =
                      let uu___7 = FStar_Syntax_Embeddings.e_list e_branch in
                      unembed' w uu___7 brs in
                    FStar_Compiler_Util.bind_opt uu___6
                      (fun brs1 ->
                         let uu___7 =
                           unembed' w e_match_returns_annotation ret_opt in
                         FStar_Compiler_Util.bind_opt uu___7
                           (fun ret_opt1 ->
                              FStar_Compiler_Effect.op_Less_Bar
                                (fun uu___8 ->
                                   FStar_Pervasives_Native.Some uu___8)
                                (FStar_Reflection_Data.Tv_Match
                                   (t2, ret_opt1, brs1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (e, uu___2)::(t1, uu___3)::(tacopt, uu___4)::(use_eq, uu___5)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_AscT.FStar_Reflection_Constants.lid
               ->
               let uu___6 = unembed' w e_term e in
               FStar_Compiler_Util.bind_opt uu___6
                 (fun e1 ->
                    let uu___7 = unembed' w e_term t1 in
                    FStar_Compiler_Util.bind_opt uu___7
                      (fun t2 ->
                         let uu___8 =
                           let uu___9 =
                             FStar_Syntax_Embeddings.e_option e_term in
                           unembed' w uu___9 tacopt in
                         FStar_Compiler_Util.bind_opt uu___8
                           (fun tacopt1 ->
                              let uu___9 =
                                unembed' w FStar_Syntax_Embeddings.e_bool
                                  use_eq in
                              FStar_Compiler_Util.bind_opt uu___9
                                (fun use_eq1 ->
                                   FStar_Compiler_Effect.op_Less_Bar
                                     (fun uu___10 ->
                                        FStar_Pervasives_Native.Some uu___10)
                                     (FStar_Reflection_Data.Tv_AscribedT
                                        (e1, t2, tacopt1, use_eq1))))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (e, uu___2)::(c, uu___3)::(tacopt, uu___4)::(use_eq, uu___5)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_AscC.FStar_Reflection_Constants.lid
               ->
               let uu___6 = unembed' w e_term e in
               FStar_Compiler_Util.bind_opt uu___6
                 (fun e1 ->
                    let uu___7 = unembed' w e_comp c in
                    FStar_Compiler_Util.bind_opt uu___7
                      (fun c1 ->
                         let uu___8 =
                           let uu___9 =
                             FStar_Syntax_Embeddings.e_option e_term in
                           unembed' w uu___9 tacopt in
                         FStar_Compiler_Util.bind_opt uu___8
                           (fun tacopt1 ->
                              let uu___9 =
                                unembed' w FStar_Syntax_Embeddings.e_bool
                                  use_eq in
                              FStar_Compiler_Util.bind_opt uu___9
                                (fun use_eq1 ->
                                   FStar_Compiler_Effect.op_Less_Bar
                                     (fun uu___10 ->
                                        FStar_Pervasives_Native.Some uu___10)
                                     (FStar_Reflection_Data.Tv_AscribedC
                                        (e1, c1, tacopt1, use_eq1))))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Tv_Unknown.FStar_Reflection_Constants.lid
               ->
               FStar_Compiler_Effect.op_Less_Bar
                 (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
                 FStar_Reflection_Data.Tv_Unknown
           | uu___2 ->
               (if w
                then
                  (let uu___4 =
                     let uu___5 =
                       let uu___6 = FStar_Syntax_Print.term_to_string t in
                       FStar_Compiler_Util.format1
                         "Not an embedded term_view: %s" uu___6 in
                     (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___4)
                else ();
                FStar_Pervasives_Native.None)) in
    mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Constants.fstar_refl_term_view
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq noaqs
let (e_lid : FStar_Ident.lid FStar_Syntax_Embeddings.embedding) =
  let embed1 rng lid =
    let uu___ = FStar_Ident.path_of_lid lid in
    embed FStar_Syntax_Embeddings.e_string_list rng uu___ in
  let unembed w t =
    let uu___ = unembed' w FStar_Syntax_Embeddings.e_string_list t in
    FStar_Compiler_Util.map_opt uu___
      (fun p -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos) in
  let uu___ = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x -> fun r -> fun uu___1 -> fun uu___2 -> embed1 r x)
    (fun x -> fun w -> fun uu___1 -> unembed w x) uu___
    FStar_Ident.string_of_lid FStar_Syntax_Syntax.ET_abstract
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed FStar_Syntax_Embeddings.e_string rng
            bvv.FStar_Reflection_Data.bv_ppname in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed FStar_Syntax_Embeddings.e_int rng
              bvv.FStar_Reflection_Data.bv_index in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 = embed e_term rng bvv.FStar_Reflection_Data.bv_sort in
            FStar_Syntax_Syntax.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.ref_Mk_bv.FStar_Reflection_Constants.t uu___
      rng in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (nm, uu___2)::(idx, uu___3)::(s, uu___4)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Mk_bv.FStar_Reflection_Constants.lid
             ->
             let uu___5 = unembed' w FStar_Syntax_Embeddings.e_string nm in
             FStar_Compiler_Util.bind_opt uu___5
               (fun nm1 ->
                  let uu___6 = unembed' w FStar_Syntax_Embeddings.e_int idx in
                  FStar_Compiler_Util.bind_opt uu___6
                    (fun idx1 ->
                       let uu___7 = unembed' w e_term s in
                       FStar_Compiler_Util.bind_opt uu___7
                         (fun s1 ->
                            FStar_Compiler_Effect.op_Less_Bar
                              (fun uu___8 ->
                                 FStar_Pervasives_Native.Some uu___8)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1
                       "Not an embedded bv_view: %s" uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Constants.fstar_refl_bv_view
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding) =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total t ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_C_Total.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.C_GTotal t ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_C_GTotal.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng pre in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed e_term rng post in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng pats in
                FStar_Syntax_Syntax.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_C_Lemma.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.C_Eff (us, eff, res, args, decrs) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Embeddings.e_list e_universe in
              embed uu___3 rng us in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed FStar_Syntax_Embeddings.e_string_list rng eff in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng res in
                FStar_Syntax_Syntax.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 = FStar_Syntax_Embeddings.e_list e_argv in
                    embed uu___9 rng args in
                  FStar_Syntax_Syntax.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      let uu___11 = FStar_Syntax_Embeddings.e_list e_term in
                      embed uu___11 rng decrs in
                    FStar_Syntax_Syntax.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_C_Eff.FStar_Reflection_Constants.t
          uu___ rng in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_Total.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w e_term t2 in
             FStar_Compiler_Util.bind_opt uu___3
               (fun t3 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_GTotal.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w e_term t2 in
             FStar_Compiler_Util.bind_opt uu___3
               (fun t3 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.C_GTotal t3))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (pre, uu___2)::(post, uu___3)::(pats, uu___4)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_Lemma.FStar_Reflection_Constants.lid
             ->
             let uu___5 = unembed' w e_term pre in
             FStar_Compiler_Util.bind_opt uu___5
               (fun pre1 ->
                  let uu___6 = unembed' w e_term post in
                  FStar_Compiler_Util.bind_opt uu___6
                    (fun post1 ->
                       let uu___7 = unembed' w e_term pats in
                       FStar_Compiler_Util.bind_opt uu___7
                         (fun pats1 ->
                            FStar_Compiler_Effect.op_Less_Bar
                              (fun uu___8 ->
                                 FStar_Pervasives_Native.Some uu___8)
                              (FStar_Reflection_Data.C_Lemma
                                 (pre1, post1, pats1)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (us, uu___2)::(eff, uu___3)::(res, uu___4)::(args1, uu___5)::
            (decrs, uu___6)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_C_Eff.FStar_Reflection_Constants.lid
             ->
             let uu___7 =
               let uu___8 = FStar_Syntax_Embeddings.e_list e_universe in
               unembed' w uu___8 us in
             FStar_Compiler_Util.bind_opt uu___7
               (fun us1 ->
                  let uu___8 =
                    unembed' w FStar_Syntax_Embeddings.e_string_list eff in
                  FStar_Compiler_Util.bind_opt uu___8
                    (fun eff1 ->
                       let uu___9 = unembed' w e_term res in
                       FStar_Compiler_Util.bind_opt uu___9
                         (fun res1 ->
                            let uu___10 =
                              let uu___11 =
                                FStar_Syntax_Embeddings.e_list e_argv in
                              unembed' w uu___11 args1 in
                            FStar_Compiler_Util.bind_opt uu___10
                              (fun args2 ->
                                 let uu___11 =
                                   let uu___12 =
                                     FStar_Syntax_Embeddings.e_list e_term in
                                   unembed' w uu___12 decrs in
                                 FStar_Compiler_Util.bind_opt uu___11
                                   (fun decrs1 ->
                                      FStar_Compiler_Effect.op_Less_Bar
                                        (fun uu___12 ->
                                           FStar_Pervasives_Native.Some
                                             uu___12)
                                        (FStar_Reflection_Data.C_Eff
                                           (us1, eff1, res1, args2, decrs1)))))))
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1
                       "Not an embedded comp_view: %s" uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_comp_view unembed_comp_view
    FStar_Reflection_Constants.fstar_refl_comp_view
let (e_order : FStar_Order.order FStar_Syntax_Embeddings.embedding) =
  let embed_order rng o =
    let r =
      match o with
      | FStar_Order.Lt -> FStar_Reflection_Constants.ord_Lt
      | FStar_Order.Eq -> FStar_Reflection_Constants.ord_Eq
      | FStar_Order.Gt -> FStar_Reflection_Constants.ord_Gt in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ord_Lt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ord_Eq_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ord_Gt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Gt
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1 "Not an embedded order: %s"
                       uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_order unembed_order FStar_Syntax_Syntax.t_order
let (e_sigelt : FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings.embedding)
  =
  let embed_sigelt rng se =
    FStar_Syntax_Util.mk_lazy se FStar_Reflection_Constants.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng) in
  let unembed_sigelt w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.format1 "Not an embedded sigelt: %s"
                  uu___5 in
              (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_sigelt unembed_sigelt
    FStar_Reflection_Constants.fstar_refl_sigelt
let (e_univ_name :
  FStar_Syntax_Syntax.univ_name FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.set_type
    FStar_Reflection_Constants.fstar_refl_univ_name e_ident
let (e_univ_names :
  FStar_Syntax_Syntax.univ_name Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_univ_name
let (e_ctor :
  (Prims.string Prims.list * FStar_Syntax_Syntax.term)
    FStar_Syntax_Embeddings.embedding)
  =
  FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_string_list
    e_term
let (e_lb_view :
  FStar_Reflection_Data.lb_view FStar_Syntax_Embeddings.embedding) =
  let embed_lb_view rng lbv =
    let uu___ =
      let uu___1 =
        let uu___2 = embed e_fv rng lbv.FStar_Reflection_Data.lb_fv in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 = embed e_univ_names rng lbv.FStar_Reflection_Data.lb_us in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 = embed e_term rng lbv.FStar_Reflection_Data.lb_typ in
            FStar_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 = embed e_term rng lbv.FStar_Reflection_Data.lb_def in
              FStar_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.ref_Mk_lb.FStar_Reflection_Constants.t uu___
      rng in
  let unembed_lb_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (fv', uu___2)::(us, uu___3)::(typ, uu___4)::(def, uu___5)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Mk_lb.FStar_Reflection_Constants.lid
             ->
             let uu___6 = unembed' w e_fv fv' in
             FStar_Compiler_Util.bind_opt uu___6
               (fun fv'1 ->
                  let uu___7 = unembed' w e_univ_names us in
                  FStar_Compiler_Util.bind_opt uu___7
                    (fun us1 ->
                       let uu___8 = unembed' w e_term typ in
                       FStar_Compiler_Util.bind_opt uu___8
                         (fun typ1 ->
                            let uu___9 = unembed' w e_term def in
                            FStar_Compiler_Util.bind_opt uu___9
                              (fun def1 ->
                                 FStar_Compiler_Effect.op_Less_Bar
                                   (fun uu___10 ->
                                      FStar_Pervasives_Native.Some uu___10)
                                   {
                                     FStar_Reflection_Data.lb_fv = fv'1;
                                     FStar_Reflection_Data.lb_us = us1;
                                     FStar_Reflection_Data.lb_typ = typ1;
                                     FStar_Reflection_Data.lb_def = def1
                                   }))))
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1
                       "Not an embedded lb_view: %s" uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_lb_view unembed_lb_view
    FStar_Reflection_Constants.fstar_refl_lb_view
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_Syntax_Embeddings.embedding) = e_term
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_attribute
let (e_letbinding :
  FStar_Syntax_Syntax.letbinding FStar_Syntax_Embeddings.embedding) =
  let embed_letbinding rng lb =
    FStar_Syntax_Util.mk_lazy lb
      FStar_Reflection_Constants.fstar_refl_letbinding
      FStar_Syntax_Syntax.Lazy_letbinding (FStar_Pervasives_Native.Some rng) in
  let unembed_letbinding w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = lb;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_letbinding;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn lb in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 ->
        (if w
         then
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.format1 "Not an embedded letbinding: %s"
                  uu___5 in
              (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  mk_emb embed_letbinding unembed_letbinding
    FStar_Reflection_Constants.fstar_refl_letbinding
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r, lbs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStar_Syntax_Embeddings.e_bool rng r in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Embeddings.e_list e_letbinding in
                embed uu___5 rng lbs in
              FStar_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Sg_Let.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStar_Syntax_Embeddings.e_string_list rng nm in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed e_univ_names rng univs in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_binders rng bs in
                FStar_Syntax_Syntax.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 = embed e_term rng t in
                  FStar_Syntax_Syntax.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      let uu___11 = FStar_Syntax_Embeddings.e_list e_ctor in
                      embed uu___11 rng dcs in
                    FStar_Syntax_Syntax.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Sg_Inductive.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Sg_Val (nm, univs, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStar_Syntax_Embeddings.e_string_list rng nm in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed e_univ_names rng univs in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng t in
                FStar_Syntax_Syntax.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Sg_Val.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Unk ->
        let uu___ =
          FStar_Reflection_Constants.ref_Unk.FStar_Reflection_Constants.t in
        {
          FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars);
          FStar_Syntax_Syntax.hash_code =
            (uu___.FStar_Syntax_Syntax.hash_code)
        } in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (nm, uu___2)::(us, uu___3)::(bs, uu___4)::(t2, uu___5)::(dcs,
                                                                    uu___6)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Sg_Inductive.FStar_Reflection_Constants.lid
             ->
             let uu___7 = unembed' w FStar_Syntax_Embeddings.e_string_list nm in
             FStar_Compiler_Util.bind_opt uu___7
               (fun nm1 ->
                  let uu___8 = unembed' w e_univ_names us in
                  FStar_Compiler_Util.bind_opt uu___8
                    (fun us1 ->
                       let uu___9 = unembed' w e_binders bs in
                       FStar_Compiler_Util.bind_opt uu___9
                         (fun bs1 ->
                            let uu___10 = unembed' w e_term t2 in
                            FStar_Compiler_Util.bind_opt uu___10
                              (fun t3 ->
                                 let uu___11 =
                                   let uu___12 =
                                     FStar_Syntax_Embeddings.e_list e_ctor in
                                   unembed' w uu___12 dcs in
                                 FStar_Compiler_Util.bind_opt uu___11
                                   (fun dcs1 ->
                                      FStar_Compiler_Effect.op_Less_Bar
                                        (fun uu___12 ->
                                           FStar_Pervasives_Native.Some
                                             uu___12)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (r, uu___2)::(lbs, uu___3)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Sg_Let.FStar_Reflection_Constants.lid
             ->
             let uu___4 = unembed' w FStar_Syntax_Embeddings.e_bool r in
             FStar_Compiler_Util.bind_opt uu___4
               (fun r1 ->
                  let uu___5 =
                    let uu___6 = FStar_Syntax_Embeddings.e_list e_letbinding in
                    unembed' w uu___6 lbs in
                  FStar_Compiler_Util.bind_opt uu___5
                    (fun lbs1 ->
                       FStar_Compiler_Effect.op_Less_Bar
                         (fun uu___6 -> FStar_Pervasives_Native.Some uu___6)
                         (FStar_Reflection_Data.Sg_Let (r1, lbs1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (nm, uu___2)::(us, uu___3)::(t2, uu___4)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Sg_Val.FStar_Reflection_Constants.lid
             ->
             let uu___5 = unembed' w FStar_Syntax_Embeddings.e_string_list nm in
             FStar_Compiler_Util.bind_opt uu___5
               (fun nm1 ->
                  let uu___6 = unembed' w e_univ_names us in
                  FStar_Compiler_Util.bind_opt uu___6
                    (fun us1 ->
                       let uu___7 = unembed' w e_term t2 in
                       FStar_Compiler_Util.bind_opt uu___7
                         (fun t3 ->
                            FStar_Compiler_Effect.op_Less_Bar
                              (fun uu___8 ->
                                 FStar_Pervasives_Native.Some uu___8)
                              (FStar_Reflection_Data.Sg_Val (nm1, us1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_Unk.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1
                       "Not an embedded sigelt_view: %s " uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_Constants.fstar_refl_sigelt_view
let (e_exp : FStar_Reflection_Data.exp FStar_Syntax_Embeddings.embedding) =
  let rec embed_exp rng e =
    let r =
      match e with
      | FStar_Reflection_Data.Unit ->
          FStar_Reflection_Constants.ref_E_Unit.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Var i ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_BigInt.string_of_big_int i in
                FStar_Syntax_Util.exp_int uu___3 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_E_Var.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1, e2) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed_exp rng e1 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = embed_exp rng e2 in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_E_Mult.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_E_Unit.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv, (i, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_E_Var.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w FStar_Syntax_Embeddings.e_int i in
             FStar_Compiler_Util.bind_opt uu___3
               (fun i1 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (e1, uu___2)::(e2, uu___3)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_E_Mult.FStar_Reflection_Constants.lid
             ->
             let uu___4 = unembed_exp w e1 in
             FStar_Compiler_Util.bind_opt uu___4
               (fun e11 ->
                  let uu___5 = unembed_exp w e2 in
                  FStar_Compiler_Util.bind_opt uu___5
                    (fun e21 ->
                       FStar_Compiler_Effect.op_Less_Bar
                         (fun uu___6 -> FStar_Pervasives_Native.Some uu___6)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1 "Not an embedded exp: %s"
                       uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed_exp unembed_exp FStar_Reflection_Constants.fstar_refl_exp
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_Syntax_Embeddings.embedding) =
  let uu___ = FStar_Syntax_Embeddings.e_tuple2 e_aqualv e_attributes in
  FStar_Syntax_Embeddings.e_tuple2 e_bv uu___
let (e_qualifier :
  FStar_Reflection_Data.qualifier FStar_Syntax_Embeddings.embedding) =
  let embed1 rng q =
    let r =
      match q with
      | FStar_Reflection_Data.Assumption ->
          FStar_Reflection_Constants.ref_qual_Assumption.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.InternalAssumption ->
          FStar_Reflection_Constants.ref_qual_InternalAssumption.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.New ->
          FStar_Reflection_Constants.ref_qual_New.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Private ->
          FStar_Reflection_Constants.ref_qual_Private.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Unfold_for_unification_and_vcgen ->
          FStar_Reflection_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Visible_default ->
          FStar_Reflection_Constants.ref_qual_Visible_default.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Irreducible ->
          FStar_Reflection_Constants.ref_qual_Irreducible.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Inline_for_extraction ->
          FStar_Reflection_Constants.ref_qual_Inline_for_extraction.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.NoExtract ->
          FStar_Reflection_Constants.ref_qual_NoExtract.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Noeq ->
          FStar_Reflection_Constants.ref_qual_Noeq.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Unopteq ->
          FStar_Reflection_Constants.ref_qual_Unopteq.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.TotalEffect ->
          FStar_Reflection_Constants.ref_qual_TotalEffect.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Logic ->
          FStar_Reflection_Constants.ref_qual_Logic.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Reifiable ->
          FStar_Reflection_Constants.ref_qual_Reifiable.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.ExceptionConstructor ->
          FStar_Reflection_Constants.ref_qual_ExceptionConstructor.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.HasMaskedEffect ->
          FStar_Reflection_Constants.ref_qual_HasMaskedEffect.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Effect ->
          FStar_Reflection_Constants.ref_qual_Effect.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.OnlyName ->
          FStar_Reflection_Constants.ref_qual_OnlyName.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.Reflectable l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_Reflectable.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_Discriminator.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_Action.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange
      | FStar_Reflection_Data.Projector (l, i) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Embeddings.e_tuple2 e_lid e_ident in
                embed uu___3 rng (l, i) in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_Projector.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange
      | FStar_Reflection_Data.RecordType (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Embeddings.e_list e_ident in
                  let uu___5 = FStar_Syntax_Embeddings.e_list e_ident in
                  FStar_Syntax_Embeddings.e_tuple2 uu___4 uu___5 in
                embed uu___3 rng (ids1, ids2) in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_RecordType.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Embeddings.e_list e_ident in
                  let uu___5 = FStar_Syntax_Embeddings.e_list e_ident in
                  FStar_Syntax_Embeddings.e_tuple2 uu___4 uu___5 in
                embed uu___3 rng (ids1, ids2) in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_RecordConstructor.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed w t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Assumption.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Assumption
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_InternalAssumption.FStar_Reflection_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.InternalAssumption
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_New.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.New
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Private.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Private
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.Unfold_for_unification_and_vcgen
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Visible_default.FStar_Reflection_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.Visible_default
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Irreducible.FStar_Reflection_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_Data.Irreducible
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Inline_for_extraction.FStar_Reflection_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.Inline_for_extraction
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_NoExtract.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.NoExtract
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Noeq.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Noeq
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Unopteq.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unopteq
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_TotalEffect.FStar_Reflection_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_Data.TotalEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Logic.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Logic
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Reifiable.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Reifiable
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_ExceptionConstructor.FStar_Reflection_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.ExceptionConstructor
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_HasMaskedEffect.FStar_Reflection_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.HasMaskedEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Effect.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Effect
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_OnlyName.FStar_Reflection_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.OnlyName
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Reflectable.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w e_lid l in
             FStar_Compiler_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Discriminator.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w e_lid l in
             FStar_Compiler_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Action.FStar_Reflection_Constants.lid
             ->
             let uu___3 = unembed' w e_lid l in
             FStar_Compiler_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Compiler_Effect.op_Less_Bar
                    (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                    (FStar_Reflection_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (payload, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_Projector.FStar_Reflection_Constants.lid
             ->
             let uu___3 =
               let uu___4 = FStar_Syntax_Embeddings.e_tuple2 e_lid e_ident in
               unembed' w uu___4 payload in
             FStar_Compiler_Util.bind_opt uu___3
               (fun uu___4 ->
                  match uu___4 with
                  | (l, i) ->
                      FStar_Compiler_Effect.op_Less_Bar
                        (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                        (FStar_Reflection_Data.Projector (l, i)))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (payload, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_RecordType.FStar_Reflection_Constants.lid
             ->
             let uu___3 =
               let uu___4 =
                 let uu___5 = FStar_Syntax_Embeddings.e_list e_ident in
                 let uu___6 = FStar_Syntax_Embeddings.e_list e_ident in
                 FStar_Syntax_Embeddings.e_tuple2 uu___5 uu___6 in
               unembed' w uu___4 payload in
             FStar_Compiler_Util.bind_opt uu___3
               (fun uu___4 ->
                  match uu___4 with
                  | (ids1, ids2) ->
                      FStar_Compiler_Effect.op_Less_Bar
                        (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                        (FStar_Reflection_Data.RecordType (ids1, ids2)))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (payload, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Constants.ref_qual_RecordConstructor.FStar_Reflection_Constants.lid
             ->
             let uu___3 =
               let uu___4 =
                 let uu___5 = FStar_Syntax_Embeddings.e_list e_ident in
                 let uu___6 = FStar_Syntax_Embeddings.e_list e_ident in
                 FStar_Syntax_Embeddings.e_tuple2 uu___5 uu___6 in
               unembed' w uu___4 payload in
             FStar_Compiler_Util.bind_opt uu___3
               (fun uu___4 ->
                  match uu___4 with
                  | (ids1, ids2) ->
                      FStar_Compiler_Effect.op_Less_Bar
                        (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                        (FStar_Reflection_Data.RecordConstructor (ids1, ids2)))
         | uu___2 ->
             (if w
              then
                (let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Compiler_Util.format1
                       "Not an embedded qualifier: %s" uu___6 in
                   (FStar_Errors_Codes.Warning_NotEmbedded, uu___5) in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___4)
              else ();
              FStar_Pervasives_Native.None)) in
  mk_emb embed1 unembed FStar_Reflection_Constants.fstar_refl_qualifier
let (e_qualifiers :
  FStar_Reflection_Data.qualifier Prims.list
    FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_qualifier
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let bv = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_Basic.inspect_bv bv in
          embed e_bv_view i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.fstar_refl_pack_bv.FStar_Reflection_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let binder = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ = FStar_Reflection_Basic.inspect_binder binder in
    match uu___ with
    | (bv, (aq, attrs)) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = embed e_bv i.FStar_Syntax_Syntax.rng bv in
            FStar_Syntax_Syntax.as_arg uu___3 in
          let uu___3 =
            let uu___4 =
              let uu___5 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq in
              FStar_Syntax_Syntax.as_arg uu___5 in
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  embed e_attributes i.FStar_Syntax_Syntax.rng attrs in
                FStar_Syntax_Syntax.as_arg uu___7 in
              [uu___6] in
            uu___4 :: uu___5 in
          uu___2 :: uu___3 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.fstar_refl_pack_binder.FStar_Reflection_Constants.t
          uu___1 i.FStar_Syntax_Syntax.rng
let (unfold_lazy_letbinding :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let lb = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let lbv = FStar_Reflection_Basic.inspect_lb lb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed e_fv i.FStar_Syntax_Syntax.rng
            lbv.FStar_Reflection_Data.lb_fv in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed e_univ_names i.FStar_Syntax_Syntax.rng
              lbv.FStar_Reflection_Data.lb_us in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed e_term i.FStar_Syntax_Syntax.rng
                lbv.FStar_Reflection_Data.lb_typ in
            FStar_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed e_term i.FStar_Syntax_Syntax.rng
                  lbv.FStar_Reflection_Data.lb_def in
              FStar_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.fstar_refl_pack_lb.FStar_Reflection_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let fv = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string in
          let uu___4 = FStar_Reflection_Basic.inspect_fv fv in
          embed uu___3 i.FStar_Syntax_Syntax.rng uu___4 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.fstar_refl_pack_fv.FStar_Reflection_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let comp = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_Basic.inspect_comp comp in
          embed e_comp_view i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.fstar_refl_pack_comp.FStar_Reflection_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_unit
let (unfold_lazy_optionstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_unit
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let sigelt = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_Basic.inspect_sigelt sigelt in
          embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.fstar_refl_pack_sigelt.FStar_Reflection_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_universe :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let u = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_Basic.inspect_universe u in
          embed e_universe_view i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.fstar_refl_pack_universe.FStar_Reflection_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng