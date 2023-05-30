open Prims
type namedv = FStar_Syntax_Syntax.bv
let curry :
  'uuuuu 'uuuuu1 'uuuuu2 .
    (('uuuuu * 'uuuuu1) -> 'uuuuu2) -> 'uuuuu -> 'uuuuu1 -> 'uuuuu2
  = fun f -> fun x -> fun y -> f (x, y)
let curry3 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    (('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu3) ->
      'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3
  = fun f -> fun x -> fun y -> fun z -> f (x, y, z)
let curry4 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 .
    (('uuuuu * 'uuuuu1 * 'uuuuu2 * 'uuuuu3) -> 'uuuuu4) ->
      'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3 -> 'uuuuu4
  = fun f -> fun x -> fun y -> fun z -> fun w -> f (x, y, z, w)
let curry5 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 'uuuuu5 .
    (('uuuuu * 'uuuuu1 * 'uuuuu2 * 'uuuuu3 * 'uuuuu4) -> 'uuuuu5) ->
      'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3 -> 'uuuuu4 -> 'uuuuu5
  = fun f -> fun x -> fun y -> fun z -> fun w -> fun v -> f (x, y, z, w, v)
let (head_fv_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Util.un_uinst hd in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (fv, args)
         | uu___2 -> FStar_Pervasives_Native.None)
let (noaqs : FStar_Syntax_Syntax.antiquotations) = (Prims.int_zero, [])
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
  FStar_Reflection_ArgEmbedder.mk_emb embed_bv unembed_bv
    FStar_Reflection_Constants.fstar_refl_bv
let (e_namedv : namedv FStar_Syntax_Embeddings.embedding) = e_bv
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
  FStar_Reflection_ArgEmbedder.mk_emb embed_binder unembed_binder
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
    FStar_Reflection_ArgEmbedder.mk_emb embed_term unembed_term
      FStar_Syntax_Syntax.t_term
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
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_term rng t in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Q_Meta.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed_aqualv _w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Q_Explicit.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 FStar_Reflection_ArgEmbedder.pure
                   FStar_Reflection_Data.Q_Explicit in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else
               if
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Reflection_Constants.ref_Q_Implicit.FStar_Reflection_Constants.lid
               then
                 (let uu___2 =
                    FStar_Reflection_ArgEmbedder.pure
                      FStar_Reflection_Data.Q_Implicit in
                  FStar_Reflection_ArgEmbedder.run args uu___2)
               else
                 if
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Reflection_Constants.ref_Q_Meta.FStar_Reflection_Constants.lid
                 then
                   (let uu___2 =
                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                        (fun uu___3 -> FStar_Reflection_Data.Q_Meta uu___3)
                        e_term in
                    FStar_Reflection_ArgEmbedder.run args uu___2)
                 else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_aqualv unembed_aqualv
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
  FStar_Reflection_ArgEmbedder.mk_emb embed_fv unembed_fv
    FStar_Reflection_Constants.fstar_refl_fv
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
  FStar_Reflection_ArgEmbedder.mk_emb embed_comp unembed_comp
    FStar_Reflection_Constants.fstar_refl_comp
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
  FStar_Reflection_ArgEmbedder.mk_emb embed_universe unembed_universe
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
            let uu___2 = FStar_Reflection_ArgEmbedder.embed e_universe rng u in
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
              FStar_Reflection_ArgEmbedder.embed uu___3 rng us in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Uv_Max.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Uv_BVar n ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Reflection_ArgEmbedder.embed
                FStar_Syntax_Embeddings.e_int rng n in
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
              FStar_Reflection_ArgEmbedder.embed uu___3 rng i in
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
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Uv_Zero.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 FStar_Reflection_ArgEmbedder.pure
                   FStar_Reflection_Data.Uv_Zero in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else
               if
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Reflection_Constants.ref_Uv_Succ.FStar_Reflection_Constants.lid
               then
                 (let uu___2 =
                    FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                      (fun uu___3 -> FStar_Reflection_Data.Uv_Succ uu___3)
                      e_universe in
                  FStar_Reflection_ArgEmbedder.run args uu___2)
               else
                 if
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Reflection_Constants.ref_Uv_Max.FStar_Reflection_Constants.lid
                 then
                   (let uu___2 =
                      let uu___3 = FStar_Syntax_Embeddings.e_list e_universe in
                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                        (fun uu___4 -> FStar_Reflection_Data.Uv_Max uu___4)
                        uu___3 in
                    FStar_Reflection_ArgEmbedder.run args uu___2)
                 else
                   if
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Reflection_Constants.ref_Uv_BVar.FStar_Reflection_Constants.lid
                   then
                     (let uu___2 =
                        FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                          (fun uu___3 -> FStar_Reflection_Data.Uv_BVar uu___3)
                          FStar_Syntax_Embeddings.e_int in
                      FStar_Reflection_ArgEmbedder.run args uu___2)
                   else
                     if
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Reflection_Constants.ref_Uv_Name.FStar_Reflection_Constants.lid
                     then
                       (let uu___2 =
                          let uu___3 =
                            FStar_Syntax_Embeddings.e_tuple2
                              FStar_Syntax_Embeddings.e_string
                              FStar_Syntax_Embeddings.e_range in
                          FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                            (fun uu___4 ->
                               FStar_Reflection_Data.Uv_Name uu___4) uu___3 in
                        FStar_Reflection_ArgEmbedder.run args uu___2)
                     else
                       if
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Reflection_Constants.ref_Uv_Unif.FStar_Reflection_Constants.lid
                       then
                         (let unemb_uuvar uu___2 =
                            match uu___2 with
                            | [] -> FStar_Pervasives_Native.None
                            | (t1, uu___3)::xs ->
                                let u =
                                  FStar_Syntax_Util.unlazy_as_t
                                    FStar_Syntax_Syntax.Lazy_universe_uvar t1 in
                                FStar_Pervasives_Native.Some (u, xs) in
                          let uu___2 =
                            FStar_Reflection_ArgEmbedder.op_Less_Dollar_Greater
                              (fun uu___3 ->
                                 FStar_Reflection_Data.Uv_Unif uu___3)
                              unemb_uuvar in
                          FStar_Reflection_ArgEmbedder.run args uu___2)
                       else
                         if
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Reflection_Constants.ref_Uv_Unk.FStar_Reflection_Constants.lid
                         then
                           (let uu___2 =
                              FStar_Reflection_ArgEmbedder.pure
                                FStar_Reflection_Data.Uv_Unk in
                            FStar_Reflection_ArgEmbedder.run args uu___2)
                         else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_universe_view
    unembed_universe_view FStar_Reflection_Constants.fstar_refl_universe_view
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
  FStar_Reflection_ArgEmbedder.mk_emb embed_env unembed_env
    FStar_Reflection_Constants.fstar_refl_env
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
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Reflection_ArgEmbedder.embed
                  FStar_Syntax_Embeddings.e_string rng s in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_C_String.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_Data.C_Range r1 ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Reflection_ArgEmbedder.embed
                  FStar_Syntax_Embeddings.e_range rng r1 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_C_Range.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_Data.C_Reify ->
          FStar_Reflection_Constants.ref_C_Reify.FStar_Reflection_Constants.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Reflection_ArgEmbedder.embed
                  FStar_Syntax_Embeddings.e_string_list rng ns in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_C_Reflect.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed_const w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_C_Unit.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 FStar_Reflection_ArgEmbedder.pure
                   FStar_Reflection_Data.C_Unit in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else
               if
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Reflection_Constants.ref_C_True.FStar_Reflection_Constants.lid
               then
                 (let uu___2 =
                    FStar_Reflection_ArgEmbedder.pure
                      FStar_Reflection_Data.C_True in
                  FStar_Reflection_ArgEmbedder.run args uu___2)
               else
                 if
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Reflection_Constants.ref_C_False.FStar_Reflection_Constants.lid
                 then
                   (let uu___2 =
                      FStar_Reflection_ArgEmbedder.pure
                        FStar_Reflection_Data.C_False in
                    FStar_Reflection_ArgEmbedder.run args uu___2)
                 else
                   if
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Reflection_Constants.ref_C_Int.FStar_Reflection_Constants.lid
                   then
                     (let uu___2 =
                        FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                          (fun uu___3 -> FStar_Reflection_Data.C_Int uu___3)
                          FStar_Syntax_Embeddings.e_int in
                      FStar_Reflection_ArgEmbedder.run args uu___2)
                   else
                     if
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Reflection_Constants.ref_C_String.FStar_Reflection_Constants.lid
                     then
                       (let uu___2 =
                          FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                            (fun uu___3 ->
                               FStar_Reflection_Data.C_String uu___3)
                            FStar_Syntax_Embeddings.e_string in
                        FStar_Reflection_ArgEmbedder.run args uu___2)
                     else
                       if
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Reflection_Constants.ref_C_Range.FStar_Reflection_Constants.lid
                       then
                         (let uu___2 =
                            FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                              (fun uu___3 ->
                                 FStar_Reflection_Data.C_Range uu___3)
                              FStar_Syntax_Embeddings.e_range in
                          FStar_Reflection_ArgEmbedder.run args uu___2)
                       else
                         if
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Reflection_Constants.ref_C_Reify.FStar_Reflection_Constants.lid
                         then
                           (let uu___2 =
                              FStar_Reflection_ArgEmbedder.pure
                                FStar_Reflection_Data.C_Reify in
                            FStar_Reflection_ArgEmbedder.run args uu___2)
                         else
                           if
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Reflection_Constants.ref_C_Reflect.FStar_Reflection_Constants.lid
                           then
                             (let uu___2 =
                                FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                  (fun uu___3 ->
                                     FStar_Reflection_Data.C_Reflect uu___3)
                                  FStar_Syntax_Embeddings.e_string_list in
                              FStar_Reflection_ArgEmbedder.run args uu___2)
                           else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_const unembed_const
    FStar_Reflection_Constants.fstar_refl_vconst
let rec e_pattern_aq :
  'uuuuu .
    'uuuuu -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding
  =
  fun aq ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant { FStar_Reflection_Data.c = c;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Pat_Constant.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Pat_Cons
          { FStar_Reflection_Data.head = head;
            FStar_Reflection_Data.univs = univs;
            FStar_Reflection_Data.subpats = subpats;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_fv rng head in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 = FStar_Syntax_Embeddings.e_list e_universe in
                    FStar_Syntax_Embeddings.e_option uu___6 in
                  FStar_Reflection_ArgEmbedder.embed uu___5 rng univs in
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
                    FStar_Reflection_ArgEmbedder.embed uu___7 rng subpats in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Pat_Cons.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Pat_Var
          { FStar_Reflection_Data.sort = sort;
            FStar_Reflection_Data.ppname = ppname;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Embeddings.e_sealed e_term in
                FStar_Reflection_ArgEmbedder.embed uu___3 rng sort in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Reflection_ArgEmbedder.embed
                    FStar_Syntax_Embeddings.e_string rng ppname in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Pat_Var.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Pat_Dot_Term
          { FStar_Reflection_Data.t = eopt;_} ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Embeddings.e_option e_term in
                FStar_Reflection_ArgEmbedder.embed uu___3 rng eopt in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Pat_Dot_Term.FStar_Reflection_Constants.t
            uu___ rng in
    let rec unembed_pattern w t =
      let pat_Constant c =
        FStar_Reflection_Data.Pat_Constant { FStar_Reflection_Data.c = c } in
      let pat_Cons head univs subpats =
        FStar_Reflection_Data.Pat_Cons
          {
            FStar_Reflection_Data.head = head;
            FStar_Reflection_Data.univs = univs;
            FStar_Reflection_Data.subpats = subpats
          } in
      let pat_Var sort ppname =
        FStar_Reflection_Data.Pat_Var
          {
            FStar_Reflection_Data.sort = sort;
            FStar_Reflection_Data.ppname = ppname
          } in
      let pat_Dot_Term t1 =
        FStar_Reflection_Data.Pat_Dot_Term { FStar_Reflection_Data.t = t1 } in
      let uu___ = head_fv_and_args t in
      FStar_Reflection_ArgEmbedder.op_let_Question uu___
        (fun uu___1 ->
           match uu___1 with
           | (fv, args) ->
               (match () with
                | uu___2 when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Reflection_Constants.ref_Pat_Constant.FStar_Reflection_Constants.lid
                    ->
                    let uu___3 =
                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                        pat_Constant e_const in
                    FStar_Reflection_ArgEmbedder.run args uu___3
                | uu___2 when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Reflection_Constants.ref_Pat_Cons.FStar_Reflection_Constants.lid
                    ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                            pat_Cons e_fv in
                        let uu___6 =
                          let uu___7 =
                            FStar_Syntax_Embeddings.e_list e_universe in
                          FStar_Syntax_Embeddings.e_option uu___7 in
                        FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                          uu___5 uu___6 in
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = e_pattern_aq aq in
                          FStar_Syntax_Embeddings.e_tuple2 uu___7
                            FStar_Syntax_Embeddings.e_bool in
                        FStar_Syntax_Embeddings.e_list uu___6 in
                      FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                        uu___4 uu___5 in
                    FStar_Reflection_ArgEmbedder.run args uu___3
                | uu___2 when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Reflection_Constants.ref_Pat_Var.FStar_Reflection_Constants.lid
                    ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 = FStar_Syntax_Embeddings.e_sealed e_term in
                        FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                          pat_Var uu___5 in
                      FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                        uu___4 FStar_Syntax_Embeddings.e_string in
                    FStar_Reflection_ArgEmbedder.run args uu___3
                | uu___2 when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Reflection_Constants.ref_Pat_Dot_Term.FStar_Reflection_Constants.lid
                    ->
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Embeddings.e_option e_term in
                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                        pat_Dot_Term uu___4 in
                    FStar_Reflection_ArgEmbedder.run args uu___3
                | uu___2 -> FStar_Pervasives_Native.None)) in
    FStar_Reflection_ArgEmbedder.mk_emb embed_pattern unembed_pattern
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
let (e_ctx_uvar_and_subst :
  FStar_Syntax_Syntax.ctx_uvar_and_subst FStar_Syntax_Embeddings.embedding) =
  let ee rng u =
    FStar_Syntax_Util.mk_lazy u FStar_Syntax_Util.t_ctx_uvar_and_sust
      FStar_Syntax_Syntax.Lazy_uvar (FStar_Pervasives_Native.Some rng) in
  let uu w t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_uvar;
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
                FStar_Compiler_Util.format1 "Not an embedded ctx_u: %s"
                  uu___5 in
              (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___3)
         else ();
         FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb ee uu
    FStar_Reflection_Constants.fstar_refl_ctx_uvar_and_subst
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
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_FVar.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_bv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_BVar.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Var.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_UInst (fv, us) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_Syntax_Embeddings.e_list e_universe in
                  FStar_Reflection_ArgEmbedder.embed uu___5 rng us in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_UInst.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_App (hd, a) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = e_term_aq aq in
                FStar_Reflection_ArgEmbedder.embed uu___3 rng hd in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_argv_aq aq in
                  FStar_Reflection_ArgEmbedder.embed uu___5 rng a in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_App.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Abs (b, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq (push aq) in
                  FStar_Reflection_ArgEmbedder.embed uu___5 rng t1 in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Abs.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Reflection_ArgEmbedder.embed e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Arrow.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Reflection_ArgEmbedder.embed e_universe rng u in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Type.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Refine (b, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq (push aq) in
                  FStar_Reflection_ArgEmbedder.embed uu___5 rng t1 in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Refine.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Const.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Uvar (u, ctx_u) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Reflection_ArgEmbedder.embed
                  FStar_Syntax_Embeddings.e_int rng u in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Reflection_ArgEmbedder.embed e_ctx_uvar_and_subst rng
                    ctx_u in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_Tv_Uvar.FStar_Reflection_Constants.t
            uu___ rng
      | FStar_Reflection_Data.Tv_Let (r, attrs, b, t1, t2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Reflection_ArgEmbedder.embed
                  FStar_Syntax_Embeddings.e_bool rng r in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_Syntax_Embeddings.e_list e_term in
                  FStar_Reflection_ArgEmbedder.embed uu___5 rng attrs in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStar_Reflection_ArgEmbedder.embed e_binder rng b in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      let uu___9 = e_term_aq aq in
                      FStar_Reflection_ArgEmbedder.embed uu___9 rng t1 in
                    FStar_Syntax_Syntax.as_arg uu___8 in
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 = e_term_aq (push aq) in
                        FStar_Reflection_ArgEmbedder.embed uu___11 rng t2 in
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
              let uu___2 =
                let uu___3 = e_term_aq aq in
                FStar_Reflection_ArgEmbedder.embed uu___3 rng t1 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Reflection_ArgEmbedder.embed
                    e_match_returns_annotation rng ret_opt in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_branch_aq aq in
                      FStar_Syntax_Embeddings.e_list uu___8 in
                    FStar_Reflection_ArgEmbedder.embed uu___7 rng brs in
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
              let uu___2 =
                let uu___3 = e_term_aq aq in
                FStar_Reflection_ArgEmbedder.embed uu___3 rng e in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq aq in
                  FStar_Reflection_ArgEmbedder.embed uu___5 rng t1 in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu___8 in
                    FStar_Reflection_ArgEmbedder.embed uu___7 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStar_Reflection_ArgEmbedder.embed
                        FStar_Syntax_Embeddings.e_bool rng use_eq in
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
              let uu___2 =
                let uu___3 = e_term_aq aq in
                FStar_Reflection_ArgEmbedder.embed uu___3 rng e in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Reflection_ArgEmbedder.embed e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu___8 in
                    FStar_Reflection_ArgEmbedder.embed uu___7 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStar_Reflection_ArgEmbedder.embed
                        FStar_Syntax_Embeddings.e_bool rng use_eq in
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
          }
      | FStar_Reflection_Data.Tv_Unsupp ->
          let uu___ =
            FStar_Reflection_Constants.ref_Tv_Unsupp.FStar_Reflection_Constants.t in
          {
            FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars);
            FStar_Syntax_Syntax.hash_code =
              (uu___.FStar_Syntax_Syntax.hash_code)
          } in
    let unembed_term_view w t =
      let uu___ = head_fv_and_args t in
      FStar_Reflection_ArgEmbedder.op_let_Question uu___
        (fun uu___1 ->
           match uu___1 with
           | (fv, args) ->
               let xTv_Let a b c d e =
                 FStar_Reflection_Data.Tv_Let (a, b, c, d, e) in
               if
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Reflection_Constants.ref_Tv_FVar.FStar_Reflection_Constants.lid
               then
                 let uu___2 =
                   FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                     (fun uu___3 -> FStar_Reflection_Data.Tv_FVar uu___3)
                     e_fv in
                 FStar_Reflection_ArgEmbedder.run args uu___2
               else
                 if
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Reflection_Constants.ref_Tv_BVar.FStar_Reflection_Constants.lid
                 then
                   (let uu___2 =
                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                        (fun uu___3 -> FStar_Reflection_Data.Tv_BVar uu___3)
                        e_bv in
                    FStar_Reflection_ArgEmbedder.run args uu___2)
                 else
                   if
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Reflection_Constants.ref_Tv_Var.FStar_Reflection_Constants.lid
                   then
                     (let uu___2 =
                        FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                          (fun uu___3 -> FStar_Reflection_Data.Tv_Var uu___3)
                          e_namedv in
                      FStar_Reflection_ArgEmbedder.run args uu___2)
                   else
                     if
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Reflection_Constants.ref_Tv_UInst.FStar_Reflection_Constants.lid
                     then
                       (let uu___2 =
                          let uu___3 =
                            FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                              (curry
                                 (fun uu___4 ->
                                    FStar_Reflection_Data.Tv_UInst uu___4))
                              e_fv in
                          let uu___4 =
                            FStar_Syntax_Embeddings.e_list e_universe in
                          FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                            uu___3 uu___4 in
                        FStar_Reflection_ArgEmbedder.run args uu___2)
                     else
                       if
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Reflection_Constants.ref_Tv_App.FStar_Reflection_Constants.lid
                       then
                         (let uu___2 =
                            let uu___3 =
                              let uu___4 = e_term_aq aq in
                              FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                (curry
                                   (fun uu___5 ->
                                      FStar_Reflection_Data.Tv_App uu___5))
                                uu___4 in
                            let uu___4 = e_argv_aq aq in
                            FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                              uu___3 uu___4 in
                          FStar_Reflection_ArgEmbedder.run args uu___2)
                       else
                         if
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Reflection_Constants.ref_Tv_Abs.FStar_Reflection_Constants.lid
                         then
                           (let uu___2 =
                              let uu___3 =
                                FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                  (curry
                                     (fun uu___4 ->
                                        FStar_Reflection_Data.Tv_Abs uu___4))
                                  e_binder in
                              let uu___4 = e_term_aq (push aq) in
                              FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                uu___3 uu___4 in
                            FStar_Reflection_ArgEmbedder.run args uu___2)
                         else
                           if
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Reflection_Constants.ref_Tv_Arrow.FStar_Reflection_Constants.lid
                           then
                             (let uu___2 =
                                let uu___3 =
                                  FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                    (curry
                                       (fun uu___4 ->
                                          FStar_Reflection_Data.Tv_Arrow
                                            uu___4)) e_binder in
                                FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                  uu___3 e_comp in
                              FStar_Reflection_ArgEmbedder.run args uu___2)
                           else
                             if
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Reflection_Constants.ref_Tv_Type.FStar_Reflection_Constants.lid
                             then
                               (let uu___2 =
                                  FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                    (fun uu___3 ->
                                       FStar_Reflection_Data.Tv_Type uu___3)
                                    e_universe in
                                FStar_Reflection_ArgEmbedder.run args uu___2)
                             else
                               if
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Reflection_Constants.ref_Tv_Refine.FStar_Reflection_Constants.lid
                               then
                                 (let uu___2 =
                                    let uu___3 =
                                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                        (curry
                                           (fun uu___4 ->
                                              FStar_Reflection_Data.Tv_Refine
                                                uu___4)) e_binder in
                                    let uu___4 = e_term_aq (push aq) in
                                    FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                      uu___3 uu___4 in
                                  FStar_Reflection_ArgEmbedder.run args
                                    uu___2)
                               else
                                 if
                                   FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Reflection_Constants.ref_Tv_Const.FStar_Reflection_Constants.lid
                                 then
                                   (let uu___2 =
                                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                        (fun uu___3 ->
                                           FStar_Reflection_Data.Tv_Const
                                             uu___3) e_const in
                                    FStar_Reflection_ArgEmbedder.run args
                                      uu___2)
                                 else
                                   if
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Reflection_Constants.ref_Tv_Uvar.FStar_Reflection_Constants.lid
                                   then
                                     (let uu___2 =
                                        let uu___3 =
                                          FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                            (curry
                                               (fun uu___4 ->
                                                  FStar_Reflection_Data.Tv_Uvar
                                                    uu___4))
                                            FStar_Syntax_Embeddings.e_int in
                                        FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                          uu___3 e_ctx_uvar_and_subst in
                                      FStar_Reflection_ArgEmbedder.run args
                                        uu___2)
                                   else
                                     if
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Reflection_Constants.ref_Tv_Let.FStar_Reflection_Constants.lid
                                     then
                                       (let uu___2 =
                                          let uu___3 =
                                            let uu___4 =
                                              let uu___5 =
                                                let uu___6 =
                                                  FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                    xTv_Let
                                                    FStar_Syntax_Embeddings.e_bool in
                                                let uu___7 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    e_term in
                                                FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                                  uu___6 uu___7 in
                                              FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                                uu___5 e_binder in
                                            let uu___5 = e_term_aq aq in
                                            FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                              uu___4 uu___5 in
                                          let uu___4 = e_term_aq (push aq) in
                                          FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                            uu___3 uu___4 in
                                        FStar_Reflection_ArgEmbedder.run args
                                          uu___2)
                                     else
                                       if
                                         FStar_Syntax_Syntax.fv_eq_lid fv
                                           FStar_Reflection_Constants.ref_Tv_Match.FStar_Reflection_Constants.lid
                                       then
                                         (let uu___2 =
                                            let uu___3 =
                                              let uu___4 =
                                                let uu___5 = e_term_aq aq in
                                                FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                  (curry3
                                                     (fun uu___6 ->
                                                        FStar_Reflection_Data.Tv_Match
                                                          uu___6)) uu___5 in
                                              FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                                uu___4
                                                e_match_returns_annotation in
                                            let uu___4 =
                                              let uu___5 = e_branch_aq aq in
                                              FStar_Syntax_Embeddings.e_list
                                                uu___5 in
                                            FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                              uu___3 uu___4 in
                                          FStar_Reflection_ArgEmbedder.run
                                            args uu___2)
                                       else
                                         if
                                           FStar_Syntax_Syntax.fv_eq_lid fv
                                             FStar_Reflection_Constants.ref_Tv_AscT.FStar_Reflection_Constants.lid
                                         then
                                           (let uu___2 =
                                              let uu___3 =
                                                let uu___4 =
                                                  let uu___5 =
                                                    let uu___6 = e_term_aq aq in
                                                    FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                      (curry4
                                                         (fun uu___7 ->
                                                            FStar_Reflection_Data.Tv_AscribedT
                                                              uu___7)) uu___6 in
                                                  let uu___6 = e_term_aq aq in
                                                  FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                                    uu___5 uu___6 in
                                                let uu___5 =
                                                  let uu___6 = e_term_aq aq in
                                                  FStar_Syntax_Embeddings.e_option
                                                    uu___6 in
                                                FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                                  uu___4 uu___5 in
                                              FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                                uu___3
                                                FStar_Syntax_Embeddings.e_bool in
                                            FStar_Reflection_ArgEmbedder.run
                                              args uu___2)
                                         else
                                           if
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Reflection_Constants.ref_Tv_AscC.FStar_Reflection_Constants.lid
                                           then
                                             (let uu___2 =
                                                let uu___3 =
                                                  let uu___4 =
                                                    let uu___5 =
                                                      let uu___6 =
                                                        e_term_aq aq in
                                                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                        (curry4
                                                           (fun uu___7 ->
                                                              FStar_Reflection_Data.Tv_AscribedC
                                                                uu___7))
                                                        uu___6 in
                                                    FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                                      uu___5 e_comp in
                                                  let uu___5 =
                                                    let uu___6 = e_term_aq aq in
                                                    FStar_Syntax_Embeddings.e_option
                                                      uu___6 in
                                                  FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                                    uu___4 uu___5 in
                                                FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                                  uu___3
                                                  FStar_Syntax_Embeddings.e_bool in
                                              FStar_Reflection_ArgEmbedder.run
                                                args uu___2)
                                           else
                                             if
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStar_Reflection_Constants.ref_Tv_Unknown.FStar_Reflection_Constants.lid
                                             then
                                               (let uu___2 =
                                                  FStar_Reflection_ArgEmbedder.pure
                                                    FStar_Reflection_Data.Tv_Unknown in
                                                FStar_Reflection_ArgEmbedder.run
                                                  args uu___2)
                                             else
                                               if
                                                 FStar_Syntax_Syntax.fv_eq_lid
                                                   fv
                                                   FStar_Reflection_Constants.ref_Tv_Unsupp.FStar_Reflection_Constants.lid
                                               then
                                                 (let uu___2 =
                                                    FStar_Reflection_ArgEmbedder.pure
                                                      FStar_Reflection_Data.Tv_Unsupp in
                                                  FStar_Reflection_ArgEmbedder.run
                                                    args uu___2)
                                               else
                                                 FStar_Pervasives_Native.None) in
    FStar_Reflection_ArgEmbedder.mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Constants.fstar_refl_term_view
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq noaqs
let (e_lid : FStar_Ident.lid FStar_Syntax_Embeddings.embedding) =
  let embed rng lid =
    let uu___ = FStar_Ident.path_of_lid lid in
    FStar_Reflection_ArgEmbedder.embed FStar_Syntax_Embeddings.e_string_list
      rng uu___ in
  let unembed w t =
    let uu___ =
      FStar_Reflection_ArgEmbedder.unembed' w
        FStar_Syntax_Embeddings.e_string_list t in
    FStar_Compiler_Util.map_opt uu___
      (fun p -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos) in
  let uu___ = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x -> fun r -> fun uu___1 -> fun uu___2 -> embed r x)
    (fun x -> fun w -> fun uu___1 -> unembed w x) uu___
    FStar_Ident.string_of_lid FStar_Syntax_Syntax.ET_abstract
let (e_namedv_view :
  FStar_Reflection_Data.namedv_view FStar_Syntax_Embeddings.embedding) =
  let embed_namedv_view rng namedvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Reflection_ArgEmbedder.embed FStar_Syntax_Embeddings.e_int
            rng namedvv.FStar_Reflection_Data.uniq in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 = FStar_Syntax_Embeddings.e_sealed e_term in
            FStar_Reflection_ArgEmbedder.embed uu___5 rng
              namedvv.FStar_Reflection_Data.sort1 in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                FStar_Syntax_Embeddings.e_sealed
                  FStar_Syntax_Embeddings.e_string in
              FStar_Reflection_ArgEmbedder.embed uu___7 rng
                namedvv.FStar_Reflection_Data.ppname1 in
            FStar_Syntax_Syntax.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.ref_Mk_namedv_view.FStar_Reflection_Constants.t
      uu___ rng in
  let unembed_namedv_view w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Mk_namedv_view.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                       (fun uu___5 ->
                          fun uu___6 ->
                            fun uu___7 ->
                              {
                                FStar_Reflection_Data.uniq = uu___5;
                                FStar_Reflection_Data.sort1 = uu___6;
                                FStar_Reflection_Data.ppname1 = uu___7
                              }) FStar_Syntax_Embeddings.e_int in
                   let uu___5 = FStar_Syntax_Embeddings.e_sealed e_term in
                   FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                     uu___4 uu___5 in
                 let uu___4 =
                   FStar_Syntax_Embeddings.e_sealed
                     FStar_Syntax_Embeddings.e_string in
                 FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                   uu___3 uu___4 in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_namedv_view unembed_namedv_view
    FStar_Reflection_Constants.fstar_refl_namedv_view
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Reflection_ArgEmbedder.embed FStar_Syntax_Embeddings.e_int
            rng bvv.FStar_Reflection_Data.index in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 = FStar_Syntax_Embeddings.e_sealed e_term in
            FStar_Reflection_ArgEmbedder.embed uu___5 rng
              bvv.FStar_Reflection_Data.sort2 in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                FStar_Syntax_Embeddings.e_sealed
                  FStar_Syntax_Embeddings.e_string in
              FStar_Reflection_ArgEmbedder.embed uu___7 rng
                bvv.FStar_Reflection_Data.ppname2 in
            FStar_Syntax_Syntax.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.ref_Mk_bv_view.FStar_Reflection_Constants.t
      uu___ rng in
  let unembed_bv_view w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Mk_bv_view.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                       (fun uu___5 ->
                          fun uu___6 ->
                            fun uu___7 ->
                              {
                                FStar_Reflection_Data.index = uu___5;
                                FStar_Reflection_Data.sort2 = uu___6;
                                FStar_Reflection_Data.ppname2 = uu___7
                              }) FStar_Syntax_Embeddings.e_int in
                   let uu___5 = FStar_Syntax_Embeddings.e_sealed e_term in
                   FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                     uu___4 uu___5 in
                 let uu___4 =
                   FStar_Syntax_Embeddings.e_sealed
                     FStar_Syntax_Embeddings.e_string in
                 FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                   uu___3 uu___4 in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Constants.fstar_refl_bv_view
let (e_binding :
  FStar_Reflection_Data.binding FStar_Syntax_Embeddings.embedding) =
  let embed rng bindingv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Reflection_ArgEmbedder.embed FStar_Syntax_Embeddings.e_int
            rng bindingv.FStar_Reflection_Data.uniq1 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStar_Reflection_ArgEmbedder.embed e_term rng
              bindingv.FStar_Reflection_Data.sort4 in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                FStar_Syntax_Embeddings.e_sealed
                  FStar_Syntax_Embeddings.e_string in
              FStar_Reflection_ArgEmbedder.embed uu___7 rng
                bindingv.FStar_Reflection_Data.ppname4 in
            FStar_Syntax_Syntax.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.ref_Mk_binding.FStar_Reflection_Constants.t
      uu___ rng in
  let unembed w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Mk_binding.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                       (fun uu___5 ->
                          fun uu___6 ->
                            fun uu___7 ->
                              {
                                FStar_Reflection_Data.uniq1 = uu___5;
                                FStar_Reflection_Data.sort4 = uu___6;
                                FStar_Reflection_Data.ppname4 = uu___7
                              }) FStar_Syntax_Embeddings.e_int in
                   FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                     uu___4 e_term in
                 let uu___4 =
                   FStar_Syntax_Embeddings.e_sealed
                     FStar_Syntax_Embeddings.e_string in
                 FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                   uu___3 uu___4 in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed unembed
    FStar_Reflection_Constants.fstar_refl_binding
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_Syntax_Embeddings.embedding) = e_term
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_attribute
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_Syntax_Embeddings.embedding) =
  let embed_binder_view rng bview =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Reflection_ArgEmbedder.embed e_term rng
            bview.FStar_Reflection_Data.sort3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStar_Reflection_ArgEmbedder.embed e_aqualv rng
              bview.FStar_Reflection_Data.qual in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStar_Reflection_ArgEmbedder.embed e_attributes rng
                bview.FStar_Reflection_Data.attrs in
            FStar_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                let uu___9 =
                  FStar_Syntax_Embeddings.e_sealed
                    FStar_Syntax_Embeddings.e_string in
                FStar_Reflection_ArgEmbedder.embed uu___9 rng
                  bview.FStar_Reflection_Data.ppname3 in
              FStar_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.ref_Mk_binder_view.FStar_Reflection_Constants.t
      uu___ rng in
  let unembed_binder_view w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Mk_binder_view.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                         (fun uu___6 ->
                            fun uu___7 ->
                              fun uu___8 ->
                                fun uu___9 ->
                                  {
                                    FStar_Reflection_Data.sort3 = uu___6;
                                    FStar_Reflection_Data.qual = uu___7;
                                    FStar_Reflection_Data.attrs = uu___8;
                                    FStar_Reflection_Data.ppname3 = uu___9
                                  }) e_term in
                     FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                       uu___5 e_aqualv in
                   let uu___5 = FStar_Syntax_Embeddings.e_list e_term in
                   FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                     uu___4 uu___5 in
                 let uu___4 =
                   FStar_Syntax_Embeddings.e_sealed
                     FStar_Syntax_Embeddings.e_string in
                 FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                   uu___3 uu___4 in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_binder_view unembed_binder_view
    FStar_Reflection_Constants.fstar_refl_binder_view
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding) =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Reflection_ArgEmbedder.embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_C_Total.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.C_GTotal t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Reflection_ArgEmbedder.embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_C_GTotal.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Reflection_ArgEmbedder.embed e_term rng pre in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Reflection_ArgEmbedder.embed e_term rng post in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStar_Reflection_ArgEmbedder.embed e_term rng pats in
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
              FStar_Reflection_ArgEmbedder.embed uu___3 rng us in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_Reflection_ArgEmbedder.embed
                  FStar_Syntax_Embeddings.e_string_list rng eff in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStar_Reflection_ArgEmbedder.embed e_term rng res in
                FStar_Syntax_Syntax.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 = FStar_Syntax_Embeddings.e_list e_argv in
                    FStar_Reflection_ArgEmbedder.embed uu___9 rng args in
                  FStar_Syntax_Syntax.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      let uu___11 = FStar_Syntax_Embeddings.e_list e_term in
                      FStar_Reflection_ArgEmbedder.embed uu___11 rng decrs in
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
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_C_Total.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                   (fun uu___3 -> FStar_Reflection_Data.C_Total uu___3)
                   e_term in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else
               if
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Reflection_Constants.ref_C_GTotal.FStar_Reflection_Constants.lid
               then
                 (let uu___2 =
                    FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                      (fun uu___3 -> FStar_Reflection_Data.C_GTotal uu___3)
                      e_term in
                  FStar_Reflection_ArgEmbedder.run args uu___2)
               else
                 if
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Reflection_Constants.ref_C_Lemma.FStar_Reflection_Constants.lid
                 then
                   (let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                            (curry3
                               (fun uu___5 ->
                                  FStar_Reflection_Data.C_Lemma uu___5))
                            e_term in
                        FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                          uu___4 e_term in
                      FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                        uu___3 e_term in
                    FStar_Reflection_ArgEmbedder.run args uu___2)
                 else
                   if
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Reflection_Constants.ref_C_Eff.FStar_Reflection_Constants.lid
                   then
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Embeddings.e_list e_universe in
                                FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                  (curry5
                                     (fun uu___8 ->
                                        FStar_Reflection_Data.C_Eff uu___8))
                                  uu___7 in
                              FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                                uu___6 FStar_Syntax_Embeddings.e_string_list in
                            FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                              uu___5 e_term in
                          let uu___5 = FStar_Syntax_Embeddings.e_list e_argv in
                          FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                            uu___4 uu___5 in
                        let uu___4 = FStar_Syntax_Embeddings.e_list e_term in
                        FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                          uu___3 uu___4 in
                      FStar_Reflection_ArgEmbedder.run args uu___2)
                   else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_comp_view unembed_comp_view
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
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ord_Lt_lid
             then
               let uu___2 = FStar_Reflection_ArgEmbedder.pure FStar_Order.Lt in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else
               if
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Reflection_Constants.ord_Eq_lid
               then
                 (let uu___2 =
                    FStar_Reflection_ArgEmbedder.pure FStar_Order.Eq in
                  FStar_Reflection_ArgEmbedder.run args uu___2)
               else
                 if
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Reflection_Constants.ord_Gt_lid
                 then
                   (let uu___2 =
                      FStar_Reflection_ArgEmbedder.pure FStar_Order.Gt in
                    FStar_Reflection_ArgEmbedder.run args uu___2)
                 else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_order unembed_order
    FStar_Syntax_Syntax.t_order
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
  FStar_Reflection_ArgEmbedder.mk_emb embed_sigelt unembed_sigelt
    FStar_Reflection_Constants.fstar_refl_sigelt
let (e_univ_name :
  FStar_Syntax_Syntax.univ_name FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.set_type
    FStar_Reflection_Constants.fstar_refl_univ_name e_ident
let (e_univ_names :
  FStar_Syntax_Syntax.univ_name Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_univ_name
let (e_subst_elt :
  FStar_Syntax_Syntax.subst_elt FStar_Syntax_Embeddings.embedding) =
  let ee rng e =
    match e with
    | FStar_Syntax_Syntax.DB (i, x) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Reflection_ArgEmbedder.embed
                FStar_Syntax_Embeddings.e_fsint rng i in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Reflection_ArgEmbedder.embed e_namedv rng x in
              FStar_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_DB.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Syntax_Syntax.NM (x, i) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Reflection_ArgEmbedder.embed e_namedv rng x in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_Reflection_ArgEmbedder.embed
                  FStar_Syntax_Embeddings.e_fsint rng i in
              FStar_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_NM.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Syntax_Syntax.NT (x, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Reflection_ArgEmbedder.embed e_namedv rng x in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Reflection_ArgEmbedder.embed e_term rng t in
              FStar_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_NT.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Syntax_Syntax.UN (i, u) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Reflection_ArgEmbedder.embed
                FStar_Syntax_Embeddings.e_fsint rng i in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_Reflection_ArgEmbedder.embed e_universe rng u in
              FStar_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_UN.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Syntax_Syntax.UD (u, i) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Reflection_ArgEmbedder.embed e_univ_name rng u in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_Reflection_ArgEmbedder.embed
                  FStar_Syntax_Embeddings.e_fsint rng i in
              FStar_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_UD.FStar_Reflection_Constants.t
          uu___ rng in
  let uu w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_DB.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                     (curry (fun uu___4 -> FStar_Syntax_Syntax.DB uu___4))
                     FStar_Syntax_Embeddings.e_fsint in
                 FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                   uu___3 e_namedv in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else
               if
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Reflection_Constants.ref_NM.FStar_Reflection_Constants.lid
               then
                 (let uu___2 =
                    let uu___3 =
                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                        (curry (fun uu___4 -> FStar_Syntax_Syntax.NM uu___4))
                        e_namedv in
                    FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                      uu___3 FStar_Syntax_Embeddings.e_fsint in
                  FStar_Reflection_ArgEmbedder.run args uu___2)
               else
                 if
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Reflection_Constants.ref_NT.FStar_Reflection_Constants.lid
                 then
                   (let uu___2 =
                      let uu___3 =
                        FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                          (curry
                             (fun uu___4 -> FStar_Syntax_Syntax.NT uu___4))
                          e_namedv in
                      FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                        uu___3 e_term in
                    FStar_Reflection_ArgEmbedder.run args uu___2)
                 else
                   if
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Reflection_Constants.ref_UN.FStar_Reflection_Constants.lid
                   then
                     (let uu___2 =
                        let uu___3 =
                          FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                            (curry
                               (fun uu___4 -> FStar_Syntax_Syntax.UN uu___4))
                            FStar_Syntax_Embeddings.e_fsint in
                        FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                          uu___3 e_universe in
                      FStar_Reflection_ArgEmbedder.run args uu___2)
                   else
                     if
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Reflection_Constants.ref_UD.FStar_Reflection_Constants.lid
                     then
                       (let uu___2 =
                          let uu___3 =
                            FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                              (curry
                                 (fun uu___4 -> FStar_Syntax_Syntax.UD uu___4))
                              e_univ_name in
                          FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                            uu___3 FStar_Syntax_Embeddings.e_fsint in
                        FStar_Reflection_ArgEmbedder.run args uu___2)
                     else
                       (if w
                        then
                          (let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Compiler_Util.format1
                                 "Not an embedded subst_elt: %s" uu___5 in
                             (FStar_Errors_Codes.Warning_NotEmbedded, uu___4) in
                           FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                             uu___3)
                        else ();
                        FStar_Pervasives_Native.None)) in
  FStar_Reflection_ArgEmbedder.mk_emb ee uu
    FStar_Reflection_Constants.fstar_refl_subst_elt
let (e_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_subst_elt
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
        let uu___2 =
          FStar_Reflection_ArgEmbedder.embed e_fv rng
            lbv.FStar_Reflection_Data.lb_fv in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStar_Reflection_ArgEmbedder.embed e_univ_names rng
              lbv.FStar_Reflection_Data.lb_us in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStar_Reflection_ArgEmbedder.embed e_term rng
                lbv.FStar_Reflection_Data.lb_typ in
            FStar_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                FStar_Reflection_ArgEmbedder.embed e_term rng
                  lbv.FStar_Reflection_Data.lb_def in
              FStar_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.ref_Mk_lb.FStar_Reflection_Constants.t uu___
      rng in
  let unembed_lb_view w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Mk_lb.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                         (fun uu___6 ->
                            fun uu___7 ->
                              fun uu___8 ->
                                fun uu___9 ->
                                  {
                                    FStar_Reflection_Data.lb_fv = uu___6;
                                    FStar_Reflection_Data.lb_us = uu___7;
                                    FStar_Reflection_Data.lb_typ = uu___8;
                                    FStar_Reflection_Data.lb_def = uu___9
                                  }) e_fv in
                     FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                       uu___5 e_univ_names in
                   FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                     uu___4 e_term in
                 FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                   uu___3 e_term in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_lb_view unembed_lb_view
    FStar_Reflection_Constants.fstar_refl_lb_view
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
  FStar_Reflection_ArgEmbedder.mk_emb embed_letbinding unembed_letbinding
    FStar_Reflection_Constants.fstar_refl_letbinding
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r, lbs) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Reflection_ArgEmbedder.embed
                FStar_Syntax_Embeddings.e_bool rng r in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Embeddings.e_list e_letbinding in
                FStar_Reflection_ArgEmbedder.embed uu___5 rng lbs in
              FStar_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Constants.ref_Sg_Let.FStar_Reflection_Constants.t
          uu___ rng
    | FStar_Reflection_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Reflection_ArgEmbedder.embed
                FStar_Syntax_Embeddings.e_string_list rng nm in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_Reflection_ArgEmbedder.embed e_univ_names rng univs in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStar_Reflection_ArgEmbedder.embed e_binders rng bs in
                FStar_Syntax_Syntax.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStar_Reflection_ArgEmbedder.embed e_term rng t in
                  FStar_Syntax_Syntax.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      let uu___11 = FStar_Syntax_Embeddings.e_list e_ctor in
                      FStar_Reflection_ArgEmbedder.embed uu___11 rng dcs in
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
            let uu___2 =
              FStar_Reflection_ArgEmbedder.embed
                FStar_Syntax_Embeddings.e_string_list rng nm in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_Reflection_ArgEmbedder.embed e_univ_names rng univs in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_Reflection_ArgEmbedder.embed e_term rng t in
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
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_Sg_Inductive.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                           (curry5
                              (fun uu___7 ->
                                 FStar_Reflection_Data.Sg_Inductive uu___7))
                           FStar_Syntax_Embeddings.e_string_list in
                       FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                         uu___6 e_univ_names in
                     FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                       uu___5 e_binders in
                   FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                     uu___4 e_term in
                 let uu___4 = FStar_Syntax_Embeddings.e_list e_ctor in
                 FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                   uu___3 uu___4 in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else
               if
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Reflection_Constants.ref_Sg_Let.FStar_Reflection_Constants.lid
               then
                 (let uu___2 =
                    let uu___3 =
                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                        (curry
                           (fun uu___4 -> FStar_Reflection_Data.Sg_Let uu___4))
                        FStar_Syntax_Embeddings.e_bool in
                    let uu___4 = FStar_Syntax_Embeddings.e_list e_letbinding in
                    FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                      uu___3 uu___4 in
                  FStar_Reflection_ArgEmbedder.run args uu___2)
               else
                 if
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Reflection_Constants.ref_Sg_Val.FStar_Reflection_Constants.lid
                 then
                   (let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                            (curry3
                               (fun uu___5 ->
                                  FStar_Reflection_Data.Sg_Val uu___5))
                            FStar_Syntax_Embeddings.e_string_list in
                        FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                          uu___4 e_univ_names in
                      FStar_Reflection_ArgEmbedder.op_Less_Star_Star_Greater
                        uu___3 e_term in
                    FStar_Reflection_ArgEmbedder.run args uu___2)
                 else
                   if
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Reflection_Constants.ref_Unk.FStar_Reflection_Constants.lid
                   then
                     (let uu___2 =
                        FStar_Reflection_ArgEmbedder.pure
                          FStar_Reflection_Data.Unk in
                      FStar_Reflection_ArgEmbedder.run args uu___2)
                   else FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_sigelt_view unembed_sigelt_view
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
            uu___ FStar_Compiler_Range_Type.dummyRange
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
            uu___ FStar_Compiler_Range_Type.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let rec unembed_exp w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             (match () with
              | uu___2 when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Reflection_Constants.ref_E_Unit.FStar_Reflection_Constants.lid
                  ->
                  let uu___3 =
                    FStar_Reflection_ArgEmbedder.pure
                      FStar_Reflection_Data.Unit in
                  FStar_Reflection_ArgEmbedder.run args uu___3
              | uu___2 when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Reflection_Constants.ref_E_Var.FStar_Reflection_Constants.lid
                  ->
                  let uu___3 =
                    FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                      (fun uu___4 -> FStar_Reflection_Data.Var uu___4)
                      FStar_Syntax_Embeddings.e_int in
                  FStar_Reflection_ArgEmbedder.run args uu___3
              | uu___2 when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Reflection_Constants.ref_E_Mult.FStar_Reflection_Constants.lid
                  ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStar_Reflection_ArgEmbedder.wrap unembed_exp in
                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Greater
                        (curry
                           (fun uu___6 -> FStar_Reflection_Data.Mult uu___6))
                        uu___5 in
                    let uu___5 =
                      FStar_Reflection_ArgEmbedder.wrap unembed_exp in
                    FStar_Reflection_ArgEmbedder.op_Less_Star_Greater uu___4
                      uu___5 in
                  FStar_Reflection_ArgEmbedder.run args uu___3
              | uu___2 -> FStar_Pervasives_Native.None)) in
  FStar_Reflection_ArgEmbedder.mk_emb embed_exp unembed_exp
    FStar_Reflection_Constants.fstar_refl_exp
let (e_qualifier :
  FStar_Reflection_Data.qualifier FStar_Syntax_Embeddings.embedding) =
  let embed rng q =
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
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_Reflectable.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_Discriminator.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_ArgEmbedder.embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_Action.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_Data.Projector (l, i) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Embeddings.e_tuple2 e_lid e_ident in
                FStar_Reflection_ArgEmbedder.embed uu___3 rng (l, i) in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_Projector.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_Data.RecordType (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Embeddings.e_list e_ident in
                  let uu___5 = FStar_Syntax_Embeddings.e_list e_ident in
                  FStar_Syntax_Embeddings.e_tuple2 uu___4 uu___5 in
                FStar_Reflection_ArgEmbedder.embed uu___3 rng (ids1, ids2) in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_RecordType.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Embeddings.e_list e_ident in
                  let uu___5 = FStar_Syntax_Embeddings.e_list e_ident in
                  FStar_Syntax_Embeddings.e_tuple2 uu___4 uu___5 in
                FStar_Reflection_ArgEmbedder.embed uu___3 rng (ids1, ids2) in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Constants.ref_qual_RecordConstructor.FStar_Reflection_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed w t =
    let uu___ = head_fv_and_args t in
    FStar_Reflection_ArgEmbedder.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Constants.ref_qual_Assumption.FStar_Reflection_Constants.lid
             then
               let uu___2 =
                 FStar_Reflection_ArgEmbedder.pure
                   FStar_Reflection_Data.Assumption in
               FStar_Reflection_ArgEmbedder.run args uu___2
             else
               if
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Reflection_Constants.ref_qual_InternalAssumption.FStar_Reflection_Constants.lid
               then
                 (let uu___2 =
                    FStar_Reflection_ArgEmbedder.pure
                      FStar_Reflection_Data.InternalAssumption in
                  FStar_Reflection_ArgEmbedder.run args uu___2)
               else
                 if
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Reflection_Constants.ref_qual_New.FStar_Reflection_Constants.lid
                 then
                   (let uu___2 =
                      FStar_Reflection_ArgEmbedder.pure
                        FStar_Reflection_Data.New in
                    FStar_Reflection_ArgEmbedder.run args uu___2)
                 else
                   if
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Reflection_Constants.ref_qual_Private.FStar_Reflection_Constants.lid
                   then
                     (let uu___2 =
                        FStar_Reflection_ArgEmbedder.pure
                          FStar_Reflection_Data.Private in
                      FStar_Reflection_ArgEmbedder.run args uu___2)
                   else
                     if
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Reflection_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Constants.lid
                     then
                       (let uu___2 =
                          FStar_Reflection_ArgEmbedder.pure
                            FStar_Reflection_Data.Unfold_for_unification_and_vcgen in
                        FStar_Reflection_ArgEmbedder.run args uu___2)
                     else
                       if
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Reflection_Constants.ref_qual_Visible_default.FStar_Reflection_Constants.lid
                       then
                         (let uu___2 =
                            FStar_Reflection_ArgEmbedder.pure
                              FStar_Reflection_Data.Visible_default in
                          FStar_Reflection_ArgEmbedder.run args uu___2)
                       else
                         if
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Reflection_Constants.ref_qual_Irreducible.FStar_Reflection_Constants.lid
                         then
                           (let uu___2 =
                              FStar_Reflection_ArgEmbedder.pure
                                FStar_Reflection_Data.Irreducible in
                            FStar_Reflection_ArgEmbedder.run args uu___2)
                         else
                           if
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Reflection_Constants.ref_qual_Inline_for_extraction.FStar_Reflection_Constants.lid
                           then
                             (let uu___2 =
                                FStar_Reflection_ArgEmbedder.pure
                                  FStar_Reflection_Data.Inline_for_extraction in
                              FStar_Reflection_ArgEmbedder.run args uu___2)
                           else
                             if
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Reflection_Constants.ref_qual_NoExtract.FStar_Reflection_Constants.lid
                             then
                               (let uu___2 =
                                  FStar_Reflection_ArgEmbedder.pure
                                    FStar_Reflection_Data.NoExtract in
                                FStar_Reflection_ArgEmbedder.run args uu___2)
                             else
                               if
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Reflection_Constants.ref_qual_Noeq.FStar_Reflection_Constants.lid
                               then
                                 (let uu___2 =
                                    FStar_Reflection_ArgEmbedder.pure
                                      FStar_Reflection_Data.Noeq in
                                  FStar_Reflection_ArgEmbedder.run args
                                    uu___2)
                               else
                                 if
                                   FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Reflection_Constants.ref_qual_Unopteq.FStar_Reflection_Constants.lid
                                 then
                                   (let uu___2 =
                                      FStar_Reflection_ArgEmbedder.pure
                                        FStar_Reflection_Data.Unopteq in
                                    FStar_Reflection_ArgEmbedder.run args
                                      uu___2)
                                 else
                                   if
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Reflection_Constants.ref_qual_TotalEffect.FStar_Reflection_Constants.lid
                                   then
                                     (let uu___2 =
                                        FStar_Reflection_ArgEmbedder.pure
                                          FStar_Reflection_Data.TotalEffect in
                                      FStar_Reflection_ArgEmbedder.run args
                                        uu___2)
                                   else
                                     if
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Reflection_Constants.ref_qual_Logic.FStar_Reflection_Constants.lid
                                     then
                                       (let uu___2 =
                                          FStar_Reflection_ArgEmbedder.pure
                                            FStar_Reflection_Data.Logic in
                                        FStar_Reflection_ArgEmbedder.run args
                                          uu___2)
                                     else
                                       if
                                         FStar_Syntax_Syntax.fv_eq_lid fv
                                           FStar_Reflection_Constants.ref_qual_Reifiable.FStar_Reflection_Constants.lid
                                       then
                                         (let uu___2 =
                                            FStar_Reflection_ArgEmbedder.pure
                                              FStar_Reflection_Data.Reifiable in
                                          FStar_Reflection_ArgEmbedder.run
                                            args uu___2)
                                       else
                                         if
                                           FStar_Syntax_Syntax.fv_eq_lid fv
                                             FStar_Reflection_Constants.ref_qual_ExceptionConstructor.FStar_Reflection_Constants.lid
                                         then
                                           (let uu___2 =
                                              FStar_Reflection_ArgEmbedder.pure
                                                FStar_Reflection_Data.ExceptionConstructor in
                                            FStar_Reflection_ArgEmbedder.run
                                              args uu___2)
                                         else
                                           if
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Reflection_Constants.ref_qual_HasMaskedEffect.FStar_Reflection_Constants.lid
                                           then
                                             (let uu___2 =
                                                FStar_Reflection_ArgEmbedder.pure
                                                  FStar_Reflection_Data.HasMaskedEffect in
                                              FStar_Reflection_ArgEmbedder.run
                                                args uu___2)
                                           else
                                             if
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStar_Reflection_Constants.ref_qual_Effect.FStar_Reflection_Constants.lid
                                             then
                                               (let uu___2 =
                                                  FStar_Reflection_ArgEmbedder.pure
                                                    FStar_Reflection_Data.Effect in
                                                FStar_Reflection_ArgEmbedder.run
                                                  args uu___2)
                                             else
                                               if
                                                 FStar_Syntax_Syntax.fv_eq_lid
                                                   fv
                                                   FStar_Reflection_Constants.ref_qual_OnlyName.FStar_Reflection_Constants.lid
                                               then
                                                 (let uu___2 =
                                                    FStar_Reflection_ArgEmbedder.pure
                                                      FStar_Reflection_Data.OnlyName in
                                                  FStar_Reflection_ArgEmbedder.run
                                                    args uu___2)
                                               else
                                                 if
                                                   FStar_Syntax_Syntax.fv_eq_lid
                                                     fv
                                                     FStar_Reflection_Constants.ref_qual_Reflectable.FStar_Reflection_Constants.lid
                                                 then
                                                   (let uu___2 =
                                                      FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                        (fun uu___3 ->
                                                           FStar_Reflection_Data.Reflectable
                                                             uu___3) e_lid in
                                                    FStar_Reflection_ArgEmbedder.run
                                                      args uu___2)
                                                 else
                                                   if
                                                     FStar_Syntax_Syntax.fv_eq_lid
                                                       fv
                                                       FStar_Reflection_Constants.ref_qual_Discriminator.FStar_Reflection_Constants.lid
                                                   then
                                                     (let uu___2 =
                                                        FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                          (fun uu___3 ->
                                                             FStar_Reflection_Data.Discriminator
                                                               uu___3) e_lid in
                                                      FStar_Reflection_ArgEmbedder.run
                                                        args uu___2)
                                                   else
                                                     if
                                                       FStar_Syntax_Syntax.fv_eq_lid
                                                         fv
                                                         FStar_Reflection_Constants.ref_qual_Action.FStar_Reflection_Constants.lid
                                                     then
                                                       (let uu___2 =
                                                          FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                            (fun uu___3 ->
                                                               FStar_Reflection_Data.Action
                                                                 uu___3)
                                                            e_lid in
                                                        FStar_Reflection_ArgEmbedder.run
                                                          args uu___2)
                                                     else
                                                       if
                                                         FStar_Syntax_Syntax.fv_eq_lid
                                                           fv
                                                           FStar_Reflection_Constants.ref_qual_Projector.FStar_Reflection_Constants.lid
                                                       then
                                                         (let uu___2 =
                                                            let uu___3 =
                                                              FStar_Syntax_Embeddings.e_tuple2
                                                                e_lid e_ident in
                                                            FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                              (fun uu___4 ->
                                                                 FStar_Reflection_Data.Projector
                                                                   uu___4)
                                                              uu___3 in
                                                          FStar_Reflection_ArgEmbedder.run
                                                            args uu___2)
                                                       else
                                                         if
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Reflection_Constants.ref_qual_RecordType.FStar_Reflection_Constants.lid
                                                         then
                                                           (let uu___2 =
                                                              let uu___3 =
                                                                let uu___4 =
                                                                  FStar_Syntax_Embeddings.e_list
                                                                    e_ident in
                                                                let uu___5 =
                                                                  FStar_Syntax_Embeddings.e_list
                                                                    e_ident in
                                                                FStar_Syntax_Embeddings.e_tuple2
                                                                  uu___4
                                                                  uu___5 in
                                                              FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                                (fun uu___4
                                                                   ->
                                                                   FStar_Reflection_Data.RecordType
                                                                    uu___4)
                                                                uu___3 in
                                                            FStar_Reflection_ArgEmbedder.run
                                                              args uu___2)
                                                         else
                                                           if
                                                             FStar_Syntax_Syntax.fv_eq_lid
                                                               fv
                                                               FStar_Reflection_Constants.ref_qual_RecordConstructor.FStar_Reflection_Constants.lid
                                                           then
                                                             (let uu___2 =
                                                                let uu___3 =
                                                                  let uu___4
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    e_ident in
                                                                  let uu___5
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    e_ident in
                                                                  FStar_Syntax_Embeddings.e_tuple2
                                                                    uu___4
                                                                    uu___5 in
                                                                FStar_Reflection_ArgEmbedder.op_Less_Dollar_Dollar_Greater
                                                                  (fun uu___4
                                                                    ->
                                                                    FStar_Reflection_Data.RecordConstructor
                                                                    uu___4)
                                                                  uu___3 in
                                                              FStar_Reflection_ArgEmbedder.run
                                                                args uu___2)
                                                           else
                                                             FStar_Pervasives_Native.None) in
  FStar_Reflection_ArgEmbedder.mk_emb embed unembed
    FStar_Reflection_Constants.fstar_refl_qualifier
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
          FStar_Reflection_ArgEmbedder.embed e_bv_view
            i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.fstar_refl_pack_bv.FStar_Reflection_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let binder = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_Basic.inspect_binder binder in
          FStar_Reflection_ArgEmbedder.embed e_binder_view
            i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.fstar_refl_pack_binder.FStar_Reflection_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_letbinding :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let lb = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let lbv = FStar_Reflection_Basic.inspect_lb lb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Reflection_ArgEmbedder.embed e_fv i.FStar_Syntax_Syntax.rng
            lbv.FStar_Reflection_Data.lb_fv in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStar_Reflection_ArgEmbedder.embed e_univ_names
              i.FStar_Syntax_Syntax.rng lbv.FStar_Reflection_Data.lb_us in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStar_Reflection_ArgEmbedder.embed e_term
                i.FStar_Syntax_Syntax.rng lbv.FStar_Reflection_Data.lb_typ in
            FStar_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                FStar_Reflection_ArgEmbedder.embed e_term
                  i.FStar_Syntax_Syntax.rng lbv.FStar_Reflection_Data.lb_def in
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
          FStar_Reflection_ArgEmbedder.embed uu___3 i.FStar_Syntax_Syntax.rng
            uu___4 in
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
          FStar_Reflection_ArgEmbedder.embed e_comp_view
            i.FStar_Syntax_Syntax.rng uu___3 in
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
          FStar_Reflection_ArgEmbedder.embed e_sigelt_view
            i.FStar_Syntax_Syntax.rng uu___3 in
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
          FStar_Reflection_ArgEmbedder.embed e_universe_view
            i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Constants.fstar_refl_pack_universe.FStar_Reflection_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng