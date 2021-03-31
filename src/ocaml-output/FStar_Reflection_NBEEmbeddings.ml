open Prims
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStar_TypeChecker_NBETerm.mkFV fv (FStar_List.rev us)
          (FStar_List.rev ts)
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us)
          (FStar_List.rev ts)
let (fv_as_emb_typ : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.emb_typ) =
  fun fv ->
    let uu___ =
      let uu___1 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      (uu___1, []) in
    FStar_Syntax_Syntax.ET_app uu___
let mk_emb' :
  'uuuuu .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'uuuuu -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t -> 'uuuuu FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv -> 'uuuuu FStar_TypeChecker_NBETerm.embedding
  =
  fun x ->
    fun y ->
      fun fv ->
        let uu___ = mkFV fv [] [] in
        let uu___1 = fv_as_emb_typ fv in
        FStar_TypeChecker_NBETerm.mk_emb x y uu___ uu___1
let mk_lazy :
  'uuuuu .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'uuuuu ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb ->
    fun obj ->
      fun ty ->
        fun kind ->
          let li =
            let uu___ = FStar_Dyn.mkdyn obj in
            {
              FStar_Syntax_Syntax.blob = uu___;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            } in
          let thunk =
            FStar_Thunk.mk
              (fun uu___ ->
                 let uu___1 = FStar_Syntax_Util.unfold_lazy li in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu___1) in
          FStar_TypeChecker_NBETerm.mk_t
            (FStar_TypeChecker_NBETerm.Lazy
               ((FStar_Pervasives.Inl li), thunk))
let (e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv cb bv =
    mk_lazy cb bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv in
  let unembed_bv cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv;
           FStar_Syntax_Syntax.ltyp = uu___;
           FStar_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu___4 -> FStar_Pervasives_Native.Some uu___4) uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded bv: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv_fv
let (e_binder :
  FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding) =
  let embed_binder cb b =
    mk_lazy cb b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder in
  let unembed_binder cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder;
           FStar_Syntax_Syntax.ltyp = uu___;
           FStar_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStar_Dyn.undyn b in FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded binder: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_binder unembed_binder
    FStar_Reflection_Data.fstar_refl_binder_fv
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
          FStar_Util.bind_opt uu___
            (fun x1 ->
               let uu___1 = mapM_opt f xs in
               FStar_Util.bind_opt uu___1
                 (fun xs1 -> FStar_Pervasives_Native.Some (x1 :: xs1)))
let (e_term_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let embed_term cb t =
      let qi =
        {
          FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
          FStar_Syntax_Syntax.antiquotes = aq
        } in
      FStar_TypeChecker_NBETerm.mk_t
        (FStar_TypeChecker_NBETerm.Quote (t, qi)) in
    let rec unembed_term cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Quote (tm, qi) ->
          FStar_Pervasives_Native.Some tm
      | uu___ -> FStar_Pervasives_Native.None in
    let uu___ = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] [] in
    let uu___1 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu___;
      FStar_TypeChecker_NBETerm.emb_typ = uu___1
    }
let (e_term : FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding) =
  e_term_aq []
let (e_aqualv :
  FStar_Reflection_Data.aqualv FStar_TypeChecker_NBETerm.embedding) =
  let embed_aqualv cb q =
    match q with
    | FStar_Reflection_Data.Q_Explicit ->
        mkConstruct
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Q_Implicit ->
        mkConstruct
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Q_Meta t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu___ in
  let unembed_aqualv cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (t1, uu___)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu___1 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu___1
          (fun t2 ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  let uu___ = mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] [] in
  let uu___1 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu___ uu___1
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_list e_binder
let (e_fv : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding) =
  let embed_fv cb fv =
    mk_lazy cb fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar in
  let unembed_fv cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar;
           FStar_Syntax_Syntax.ltyp = uu___;
           FStar_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStar_Dyn.undyn b in FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded fvar: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv_fv
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp cb c =
    mk_lazy cb c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp in
  let unembed_comp cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp;
           FStar_Syntax_Syntax.ltyp = uu___;
           FStar_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStar_Dyn.undyn b in FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded comp: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp_fv
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env cb e =
    mk_lazy cb e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env in
  let unembed_env cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env;
           FStar_Syntax_Syntax.ltyp = uu___;
           FStar_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStar_Dyn.undyn b in FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded env: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_env unembed_env FStar_Reflection_Data.fstar_refl_env_fv
let (e_const :
  FStar_Reflection_Data.vconst FStar_TypeChecker_NBETerm.embedding) =
  let embed_const cb c =
    match c with
    | FStar_Reflection_Data.C_Unit ->
        mkConstruct FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.C_True ->
        mkConstruct FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.C_False ->
        mkConstruct
          FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Int i ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
                (FStar_TypeChecker_NBETerm.Constant
                   (FStar_TypeChecker_NBETerm.Int i)) in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu___
    | FStar_Reflection_Data.C_String s ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu___
    | FStar_Reflection_Data.C_Range r ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv [] uu___
    | FStar_Reflection_Data.C_Reify ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu___ in
  let unembed_const cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (i, uu___)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu___1 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i in
        FStar_Util.bind_opt uu___1
          (fun i1 ->
             FStar_All.pipe_left
               (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (s, uu___)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu___1 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s in
        FStar_Util.bind_opt uu___1
          (fun s1 ->
             FStar_All.pipe_left
               (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (r, uu___)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu___1 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r in
        FStar_Util.bind_opt uu___1
          (fun r1 ->
             FStar_All.pipe_left
               (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (ns, uu___)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu___1 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns in
        FStar_Util.bind_opt uu___1
          (fun ns1 ->
             FStar_All.pipe_left
               (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded vconst: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu___ ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_TypeChecker_NBETerm.embed e_const cb c in
              FStar_TypeChecker_NBETerm.as_arg uu___3 in
            [uu___2] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu___1
      | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu___3 in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_pattern' () in
                      FStar_TypeChecker_NBETerm.e_tuple2 uu___8
                        FStar_TypeChecker_NBETerm.e_bool in
                    FStar_TypeChecker_NBETerm.e_list uu___7 in
                  FStar_TypeChecker_NBETerm.embed uu___6 cb ps in
                FStar_TypeChecker_NBETerm.as_arg uu___5 in
              [uu___4] in
            uu___2 :: uu___3 in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu___1
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu___3 in
            [uu___2] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu___1
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu___3 in
            [uu___2] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu___1
      | FStar_Reflection_Data.Pat_Dot_Term (bv, t) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu___3 in
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_TypeChecker_NBETerm.embed e_term cb t in
                FStar_TypeChecker_NBETerm.as_arg uu___5 in
              [uu___4] in
            uu___2 :: uu___3 in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu___1 in
    let unembed_pattern cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (c, uu___1)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu___2 = FStar_TypeChecker_NBETerm.unembed e_const cb c in
          FStar_Util.bind_opt uu___2
            (fun c1 ->
               FStar_All.pipe_left
                 (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, [], (ps, uu___1)::(f, uu___2)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu___3 = FStar_TypeChecker_NBETerm.unembed e_fv cb f in
          FStar_Util.bind_opt uu___3
            (fun f1 ->
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = e_pattern' () in
                     FStar_TypeChecker_NBETerm.e_tuple2 uu___7
                       FStar_TypeChecker_NBETerm.e_bool in
                   FStar_TypeChecker_NBETerm.e_list uu___6 in
                 FStar_TypeChecker_NBETerm.unembed uu___5 cb ps in
               FStar_Util.bind_opt uu___4
                 (fun ps1 ->
                    FStar_All.pipe_left
                      (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (bv, uu___1)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu___2 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu___2
            (fun bv1 ->
               FStar_All.pipe_left
                 (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (bv, uu___1)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu___2 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu___2
            (fun bv1 ->
               FStar_All.pipe_left
                 (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, [], (t1, uu___1)::(bv, uu___2)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu___3 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu___3
            (fun bv1 ->
               let uu___4 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu___4
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu___1 ->
          ((let uu___3 =
              let uu___4 =
                let uu___5 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded pattern: %s" uu___5 in
              (FStar_Errors.Warning_NotEmbedded, uu___4) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu___3);
           FStar_Pervasives_Native.None) in
    mk_emb' embed_pattern unembed_pattern
      FStar_Reflection_Data.fstar_refl_pattern_fv
let (e_pattern :
  FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding) =
  e_pattern' ()
let (e_branch :
  FStar_Reflection_Data.branch FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_pattern e_term
let (e_argv : FStar_Reflection_Data.argv FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_tuple2 e_term e_aqualv
let (e_branch_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let uu___ = e_term_aq aq in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu___
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let uu___ = e_term_aq aq in
    FStar_TypeChecker_NBETerm.e_tuple2 uu___ e_aqualv
let (e_match_returns_annotation :
  ((FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.comp)
    FStar_Pervasives.either * FStar_Syntax_Syntax.term
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option
    FStar_TypeChecker_NBETerm.embedding)
  =
  let uu___ =
    let uu___1 = FStar_TypeChecker_NBETerm.e_either e_term e_comp in
    let uu___2 = FStar_TypeChecker_NBETerm.e_option e_term in
    FStar_TypeChecker_NBETerm.e_tuple2 uu___1 uu___2 in
  FStar_TypeChecker_NBETerm.e_option uu___
let unlazy_as_t :
  'uuuuu .
    FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t -> 'uuuuu
  =
  fun k ->
    fun t ->
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Pervasives.Inl
           { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu___;
             FStar_Syntax_Syntax.rng = uu___1;_},
           uu___2)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu___ -> failwith "Not a Lazy of the expected kind (NBE)"
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_App (hd, a) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu___3 cb hd in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_argv_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu___5 cb a in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Abs (b, t) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.embed e_binder cb b in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu___5 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.embed e_binder cb b in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_TypeChecker_NBETerm.embed e_comp cb c in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Type u ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb () in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Refine (bv, t) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu___5 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_NBETerm.embed e_const cb c in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Uvar (u, d) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Let (r, attrs, b, t1, t2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_TypeChecker_NBETerm.e_list e_term in
                  FStar_TypeChecker_NBETerm.embed uu___5 cb attrs in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStar_TypeChecker_NBETerm.embed e_bv cb b in
                  FStar_TypeChecker_NBETerm.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      let uu___9 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.embed uu___9 cb t1 in
                    FStar_TypeChecker_NBETerm.as_arg uu___8 in
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 = e_term_aq aq in
                        FStar_TypeChecker_NBETerm.embed uu___11 cb t2 in
                      FStar_TypeChecker_NBETerm.as_arg uu___10 in
                    [uu___9] in
                  uu___7 :: uu___8 in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Match (t, ret_opt, brs) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu___3 cb t in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_TypeChecker_NBETerm.embed e_match_returns_annotation
                    cb ret_opt in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_branch_aq aq in
                      FStar_TypeChecker_NBETerm.e_list uu___8 in
                    FStar_TypeChecker_NBETerm.embed uu___7 cb brs in
                  FStar_TypeChecker_NBETerm.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu___3 cb e in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu___5 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.e_option uu___8 in
                    FStar_TypeChecker_NBETerm.embed uu___7 cb tacopt in
                  FStar_TypeChecker_NBETerm.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu___3 cb e in
              FStar_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_TypeChecker_NBETerm.embed e_comp cb c in
                FStar_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.e_option uu___8 in
                    FStar_TypeChecker_NBETerm.embed uu___7 cb tacopt in
                  FStar_TypeChecker_NBETerm.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu___
      | FStar_Reflection_Data.Tv_Unknown ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            [] in
    let unembed_term_view cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Construct (fv, uu___, (b, uu___1)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu___2 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu___2
            (fun b1 ->
               FStar_All.pipe_left
                 (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct (fv, uu___, (b, uu___1)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu___2 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu___2
            (fun b1 ->
               FStar_All.pipe_left
                 (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct (fv, uu___, (f, uu___1)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu___2 = FStar_TypeChecker_NBETerm.unembed e_fv cb f in
          FStar_Util.bind_opt uu___2
            (fun f1 ->
               FStar_All.pipe_left
                 (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___, (r, uu___1)::(l, uu___2)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu___3 = FStar_TypeChecker_NBETerm.unembed e_term cb l in
          FStar_Util.bind_opt uu___3
            (fun l1 ->
               let uu___4 = FStar_TypeChecker_NBETerm.unembed e_argv cb r in
               FStar_Util.bind_opt uu___4
                 (fun r1 ->
                    FStar_All.pipe_left
                      (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___, (t1, uu___1)::(b, uu___2)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu___3 = FStar_TypeChecker_NBETerm.unembed e_binder cb b in
          FStar_Util.bind_opt uu___3
            (fun b1 ->
               let uu___4 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu___4
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___, (t1, uu___1)::(b, uu___2)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu___3 = FStar_TypeChecker_NBETerm.unembed e_binder cb b in
          FStar_Util.bind_opt uu___3
            (fun b1 ->
               let uu___4 = FStar_TypeChecker_NBETerm.unembed e_comp cb t1 in
               FStar_Util.bind_opt uu___4
                 (fun c ->
                    FStar_All.pipe_left
                      (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct (fv, uu___, (u, uu___1)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu___2 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u in
          FStar_Util.bind_opt uu___2
            (fun u1 ->
               FStar_All.pipe_left
                 (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___, (t1, uu___1)::(b, uu___2)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu___3 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu___3
            (fun b1 ->
               let uu___4 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu___4
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct (fv, uu___, (c, uu___1)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu___2 = FStar_TypeChecker_NBETerm.unembed e_const cb c in
          FStar_Util.bind_opt uu___2
            (fun c1 ->
               FStar_All.pipe_left
                 (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___, (l, uu___1)::(u, uu___2)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu___3 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u in
          FStar_Util.bind_opt uu___3
            (fun u1 ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l in
               FStar_All.pipe_left
                 (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___,
           (t2, uu___1)::(t1, uu___2)::(b, uu___3)::(attrs, uu___4)::
           (r, uu___5)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu___6 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r in
          FStar_Util.bind_opt uu___6
            (fun r1 ->
               let uu___7 =
                 let uu___8 = FStar_TypeChecker_NBETerm.e_list e_term in
                 FStar_TypeChecker_NBETerm.unembed uu___8 cb attrs in
               FStar_Util.bind_opt uu___7
                 (fun attrs1 ->
                    let uu___8 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
                    FStar_Util.bind_opt uu___8
                      (fun b1 ->
                         let uu___9 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                         FStar_Util.bind_opt uu___9
                           (fun t11 ->
                              let uu___10 =
                                FStar_TypeChecker_NBETerm.unembed e_term cb
                                  t2 in
                              FStar_Util.bind_opt uu___10
                                (fun t21 ->
                                   FStar_All.pipe_left
                                     (fun uu___11 ->
                                        FStar_Pervasives_Native.Some uu___11)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, attrs1, b1, t11, t21)))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___, (brs, uu___1)::(ret_opt, uu___2)::(t1, uu___3)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu___4 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
          FStar_Util.bind_opt uu___4
            (fun t2 ->
               let uu___5 =
                 let uu___6 = FStar_TypeChecker_NBETerm.e_list e_branch in
                 FStar_TypeChecker_NBETerm.unembed uu___6 cb brs in
               FStar_Util.bind_opt uu___5
                 (fun brs1 ->
                    let uu___6 =
                      FStar_TypeChecker_NBETerm.unembed
                        e_match_returns_annotation cb ret_opt in
                    FStar_Util.bind_opt uu___6
                      (fun ret_opt1 ->
                         FStar_All.pipe_left
                           (fun uu___7 -> FStar_Pervasives_Native.Some uu___7)
                           (FStar_Reflection_Data.Tv_Match
                              (t2, ret_opt1, brs1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___, (tacopt, uu___1)::(t1, uu___2)::(e, uu___3)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu___4 = FStar_TypeChecker_NBETerm.unembed e_term cb e in
          FStar_Util.bind_opt uu___4
            (fun e1 ->
               let uu___5 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu___5
                 (fun t2 ->
                    let uu___6 =
                      let uu___7 = FStar_TypeChecker_NBETerm.e_option e_term in
                      FStar_TypeChecker_NBETerm.unembed uu___7 cb tacopt in
                    FStar_Util.bind_opt uu___6
                      (fun tacopt1 ->
                         FStar_All.pipe_left
                           (fun uu___7 -> FStar_Pervasives_Native.Some uu___7)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu___, (tacopt, uu___1)::(c, uu___2)::(e, uu___3)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu___4 = FStar_TypeChecker_NBETerm.unembed e_term cb e in
          FStar_Util.bind_opt uu___4
            (fun e1 ->
               let uu___5 = FStar_TypeChecker_NBETerm.unembed e_comp cb c in
               FStar_Util.bind_opt uu___5
                 (fun c1 ->
                    let uu___6 =
                      let uu___7 = FStar_TypeChecker_NBETerm.e_option e_term in
                      FStar_TypeChecker_NBETerm.unembed uu___7 cb tacopt in
                    FStar_Util.bind_opt uu___6
                      (fun tacopt1 ->
                         FStar_All.pipe_left
                           (fun uu___7 -> FStar_Pervasives_Native.Some uu___7)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv, uu___, []) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun uu___1 -> FStar_Pervasives_Native.Some uu___1)
            FStar_Reflection_Data.Tv_Unknown
      | uu___ ->
          ((let uu___2 =
              let uu___3 =
                let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded term_view: %s" uu___4 in
              (FStar_Errors.Warning_NotEmbedded, uu___3) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
           FStar_Pervasives_Native.None) in
    mk_emb' embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view_fv
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq []
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view cb bvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname in
        FStar_TypeChecker_NBETerm.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index in
          FStar_TypeChecker_NBETerm.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort in
            FStar_TypeChecker_NBETerm.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu___ in
  let unembed_bv_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu___, (s, uu___1)::(idx, uu___2)::(nm, uu___3)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu___4 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm in
        FStar_Util.bind_opt uu___4
          (fun nm1 ->
             let uu___5 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx in
             FStar_Util.bind_opt uu___5
               (fun idx1 ->
                  let uu___6 = FStar_TypeChecker_NBETerm.unembed e_term cb s in
                  FStar_Util.bind_opt uu___6
                    (fun s1 ->
                       FStar_All.pipe_left
                         (fun uu___7 -> FStar_Pervasives_Native.Some uu___7)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t, md) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_TypeChecker_NBETerm.e_list e_term in
                FStar_TypeChecker_NBETerm.embed uu___5 cb md in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv [] uu___
    | FStar_Reflection_Data.C_GTotal (t, md) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_TypeChecker_NBETerm.e_list e_term in
                FStar_TypeChecker_NBETerm.embed uu___5 cb md in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.fv []
          uu___
    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_NBETerm.embed e_term cb pre in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.embed e_term cb post in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_TypeChecker_NBETerm.embed e_term cb pats in
                FStar_TypeChecker_NBETerm.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv [] uu___
    | FStar_Reflection_Data.C_Eff (us, eff, res, args) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_TypeChecker_NBETerm.e_list
                  FStar_TypeChecker_NBETerm.e_unit in
              FStar_TypeChecker_NBETerm.embed uu___3 cb us in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_string_list cb eff in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_TypeChecker_NBETerm.embed e_term cb res in
                FStar_TypeChecker_NBETerm.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 = FStar_TypeChecker_NBETerm.e_list e_argv in
                    FStar_TypeChecker_NBETerm.embed uu___9 cb args in
                  FStar_TypeChecker_NBETerm.as_arg uu___8 in
                [uu___7] in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mkConstruct FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.fv
          [] uu___ in
  let unembed_comp_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu___, (md, uu___1)::(t1, uu___2)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu___3 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu___3
          (fun t2 ->
             let uu___4 =
               let uu___5 = FStar_TypeChecker_NBETerm.e_list e_term in
               FStar_TypeChecker_NBETerm.unembed uu___5 cb md in
             FStar_Util.bind_opt uu___4
               (fun md1 ->
                  FStar_All.pipe_left
                    (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu___, (md, uu___1)::(t1, uu___2)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
        ->
        let uu___3 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu___3
          (fun t2 ->
             let uu___4 =
               let uu___5 = FStar_TypeChecker_NBETerm.e_list e_term in
               FStar_TypeChecker_NBETerm.unembed uu___5 cb md in
             FStar_Util.bind_opt uu___4
               (fun md1 ->
                  FStar_All.pipe_left
                    (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                    (FStar_Reflection_Data.C_GTotal (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu___, (post, uu___1)::(pre, uu___2)::(pats, uu___3)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu___4 = FStar_TypeChecker_NBETerm.unembed e_term cb pre in
        FStar_Util.bind_opt uu___4
          (fun pre1 ->
             let uu___5 = FStar_TypeChecker_NBETerm.unembed e_term cb post in
             FStar_Util.bind_opt uu___5
               (fun post1 ->
                  let uu___6 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb pats in
                  FStar_Util.bind_opt uu___6
                    (fun pats1 ->
                       FStar_All.pipe_left
                         (fun uu___7 -> FStar_Pervasives_Native.Some uu___7)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1, pats1)))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu___,
         (args, uu___1)::(res, uu___2)::(eff, uu___3)::(us, uu___4)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
        ->
        let uu___5 =
          let uu___6 =
            FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_unit in
          FStar_TypeChecker_NBETerm.unembed uu___6 cb us in
        FStar_Util.bind_opt uu___5
          (fun us1 ->
             let uu___6 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_string_list cb eff in
             FStar_Util.bind_opt uu___6
               (fun eff1 ->
                  let uu___7 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb res in
                  FStar_Util.bind_opt uu___7
                    (fun res1 ->
                       let uu___8 =
                         let uu___9 = FStar_TypeChecker_NBETerm.e_list e_argv in
                         FStar_TypeChecker_NBETerm.unembed uu___9 cb args in
                       FStar_Util.bind_opt uu___8
                         (fun args1 ->
                            FStar_All.pipe_left
                              (fun uu___9 ->
                                 FStar_Pervasives_Native.Some uu___9)
                              (FStar_Reflection_Data.C_Eff
                                 (us1, eff1, res1, args1))))))
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_comp_view unembed_comp_view
    FStar_Reflection_Data.fstar_refl_comp_view_fv
let (e_order : FStar_Order.order FStar_TypeChecker_NBETerm.embedding) =
  let embed_order cb o =
    match o with
    | FStar_Order.Lt -> mkConstruct FStar_Reflection_Data.ord_Lt_fv [] []
    | FStar_Order.Eq -> mkConstruct FStar_Reflection_Data.ord_Eq_fv [] []
    | FStar_Order.Gt -> mkConstruct FStar_Reflection_Data.ord_Gt_fv [] [] in
  let unembed_order cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded order: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  let uu___ =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  mk_emb' embed_order unembed_order uu___
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt cb se =
    mk_lazy cb se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt in
  let unembed_sigelt cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt;
           FStar_Syntax_Syntax.ltyp = uu___;
           FStar_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStar_Dyn.undyn b in FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt_fv
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string in
  let embed_ident cb i =
    let uu___ =
      let uu___1 = FStar_Ident.range_of_id i in
      let uu___2 = FStar_Ident.string_of_id i in (uu___1, uu___2) in
    FStar_TypeChecker_NBETerm.embed repr cb uu___ in
  let unembed_ident cb t =
    let uu___ = FStar_TypeChecker_NBETerm.unembed repr cb t in
    match uu___ with
    | FStar_Pervasives_Native.Some (rng, s) ->
        let uu___1 = FStar_Ident.mk_ident (s, rng) in
        FStar_Pervasives_Native.Some uu___1
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let range_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  let string_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  let et =
    let uu___ =
      let uu___1 = FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2 in
      let uu___2 =
        let uu___3 = fv_as_emb_typ range_fv in
        let uu___4 = let uu___5 = fv_as_emb_typ string_fv in [uu___5] in
        uu___3 :: uu___4 in
      (uu___1, uu___2) in
    FStar_Syntax_Syntax.ET_app uu___ in
  let uu___ =
    let uu___1 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    let uu___2 =
      let uu___3 =
        let uu___4 = mkFV range_fv [] [] in
        FStar_TypeChecker_NBETerm.as_arg uu___4 in
      let uu___4 =
        let uu___5 =
          let uu___6 = mkFV string_fv [] [] in
          FStar_TypeChecker_NBETerm.as_arg uu___6 in
        [uu___5] in
      uu___3 :: uu___4 in
    mkFV uu___1 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu___2 in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu___ et
let (e_univ_name :
  FStar_Syntax_Syntax.univ_name FStar_TypeChecker_NBETerm.embedding) =
  e_ident
let (e_univ_names :
  FStar_Syntax_Syntax.univ_name Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_univ_name
let (e_string_list :
  Prims.string Prims.list FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_string
let (e_ctor :
  (Prims.string Prims.list * FStar_Syntax_Syntax.term)
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_tuple2 e_string_list e_term
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt_view cb sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r, fv, univs, ty, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs in
                FStar_TypeChecker_NBETerm.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 = FStar_TypeChecker_NBETerm.embed e_term cb ty in
                  FStar_TypeChecker_NBETerm.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 = FStar_TypeChecker_NBETerm.embed e_term cb t in
                    FStar_TypeChecker_NBETerm.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu___
    | FStar_Reflection_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_NBETerm.embed e_string_list cb nm in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_TypeChecker_NBETerm.embed e_binders cb bs in
                FStar_TypeChecker_NBETerm.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 = FStar_TypeChecker_NBETerm.embed e_term cb t in
                  FStar_TypeChecker_NBETerm.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      let uu___11 = FStar_TypeChecker_NBETerm.e_list e_ctor in
                      FStar_TypeChecker_NBETerm.embed uu___11 cb dcs in
                    FStar_TypeChecker_NBETerm.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu___
    | FStar_Reflection_Data.Unk ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          [] in
  let unembed_sigelt_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu___,
         (dcs, uu___1)::(t1, uu___2)::(bs, uu___3)::(us, uu___4)::(nm,
                                                                   uu___5)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu___6 = FStar_TypeChecker_NBETerm.unembed e_string_list cb nm in
        FStar_Util.bind_opt uu___6
          (fun nm1 ->
             let uu___7 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us in
             FStar_Util.bind_opt uu___7
               (fun us1 ->
                  let uu___8 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs in
                  FStar_Util.bind_opt uu___8
                    (fun bs1 ->
                       let uu___9 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                       FStar_Util.bind_opt uu___9
                         (fun t2 ->
                            let uu___10 =
                              let uu___11 =
                                FStar_TypeChecker_NBETerm.e_list e_ctor in
                              FStar_TypeChecker_NBETerm.unembed uu___11 cb
                                dcs in
                            FStar_Util.bind_opt uu___10
                              (fun dcs1 ->
                                 FStar_All.pipe_left
                                   (fun uu___11 ->
                                      FStar_Pervasives_Native.Some uu___11)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu___,
         (t1, uu___1)::(ty, uu___2)::(univs, uu___3)::(fvar, uu___4)::
         (r, uu___5)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu___6 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r in
        FStar_Util.bind_opt uu___6
          (fun r1 ->
             let uu___7 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar in
             FStar_Util.bind_opt uu___7
               (fun fvar1 ->
                  let uu___8 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs in
                  FStar_Util.bind_opt uu___8
                    (fun univs1 ->
                       let uu___9 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty in
                       FStar_Util.bind_opt uu___9
                         (fun ty1 ->
                            let uu___10 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                            FStar_Util.bind_opt uu___10
                              (fun t2 ->
                                 FStar_All.pipe_left
                                   (fun uu___11 ->
                                      FStar_Pervasives_Native.Some uu___11)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar1, univs1, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_Data.fstar_refl_sigelt_view_fv
let (e_exp : FStar_Reflection_Data.exp FStar_TypeChecker_NBETerm.embedding) =
  let rec embed_exp cb e =
    match e with
    | FStar_Reflection_Data.Unit ->
        mkConstruct FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Var i ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_TypeChecker_NBETerm.mk_t
                (FStar_TypeChecker_NBETerm.Constant
                   (FStar_TypeChecker_NBETerm.Int i)) in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu___
    | FStar_Reflection_Data.Mult (e1, e2) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed_exp cb e1 in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed_exp cb e2 in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu___ in
  let rec unembed_exp cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv, uu___, (i, uu___1)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu___2 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i in
        FStar_Util.bind_opt uu___2
          (fun i1 ->
             FStar_All.pipe_left
               (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu___, (e2, uu___1)::(e1, uu___2)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu___3 = unembed_exp cb e1 in
        FStar_Util.bind_opt uu___3
          (fun e11 ->
             let uu___4 = unembed_exp cb e2 in
             FStar_Util.bind_opt uu___4
               (fun e21 ->
                  FStar_All.pipe_left
                    (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded exp: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp_fv
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  let uu___ =
    let uu___1 = FStar_TypeChecker_NBETerm.e_list e_term in
    FStar_TypeChecker_NBETerm.e_tuple2 e_aqualv uu___1 in
  FStar_TypeChecker_NBETerm.e_tuple2 e_bv uu___
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding) = e_term
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_attribute
let (e_lid : FStar_Ident.lid FStar_TypeChecker_NBETerm.embedding) =
  let embed rng lid =
    let uu___ = FStar_Ident.path_of_lid lid in
    FStar_TypeChecker_NBETerm.embed e_string_list rng uu___ in
  let unembed cb t =
    let uu___ = FStar_TypeChecker_NBETerm.unembed e_string_list cb t in
    FStar_Util.map_opt uu___
      (fun p -> FStar_Ident.lid_of_path p FStar_Range.dummyRange) in
  let uu___ = mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] [] in
  let uu___1 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed unembed uu___ uu___1
let (e_qualifier :
  FStar_Reflection_Data.qualifier FStar_TypeChecker_NBETerm.embedding) =
  let embed cb q =
    match q with
    | FStar_Reflection_Data.Assumption ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.New ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Private ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.fv []
          []
    | FStar_Reflection_Data.Unfold_for_unification_and_vcgen ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Visible_default ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Irreducible ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Inline_for_extraction ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.NoExtract ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Noeq ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Unopteq ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.fv []
          []
    | FStar_Reflection_Data.TotalEffect ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Logic ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Reifiable ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.ExceptionConstructor ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.HasMaskedEffect ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Effect ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.fv []
          []
    | FStar_Reflection_Data.OnlyName ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.fv []
          []
    | FStar_Reflection_Data.Reflectable l ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.fv
          [] uu___
    | FStar_Reflection_Data.Discriminator l ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.fv
          [] uu___
    | FStar_Reflection_Data.Action l ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.fv []
          uu___
    | FStar_Reflection_Data.Projector (l, i) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.embed e_ident cb i in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.fv
          [] uu___
    | FStar_Reflection_Data.RecordType (ids1, ids2) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_TypeChecker_NBETerm.e_list e_ident in
              FStar_TypeChecker_NBETerm.embed uu___3 cb ids1 in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_TypeChecker_NBETerm.e_list e_ident in
                FStar_TypeChecker_NBETerm.embed uu___5 cb ids2 in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.fv
          [] uu___
    | FStar_Reflection_Data.RecordConstructor (ids1, ids2) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_TypeChecker_NBETerm.e_list e_ident in
              FStar_TypeChecker_NBETerm.embed uu___3 cb ids1 in
            FStar_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStar_TypeChecker_NBETerm.e_list e_ident in
                FStar_TypeChecker_NBETerm.embed uu___5 cb ids2 in
              FStar_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.fv
          [] uu___ in
  let unembed cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Assumption
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.New
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Private
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.lid
        ->
        FStar_Pervasives_Native.Some
          FStar_Reflection_Data.Unfold_for_unification_and_vcgen
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Visible_default
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Irreducible
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.lid
        ->
        FStar_Pervasives_Native.Some
          FStar_Reflection_Data.Inline_for_extraction
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.NoExtract
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Noeq
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unopteq
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.TotalEffect
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Logic
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Reifiable
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.lid
        ->
        FStar_Pervasives_Native.Some
          FStar_Reflection_Data.ExceptionConstructor
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.HasMaskedEffect
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Effect
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.OnlyName
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (l, uu___)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
        ->
        let uu___1 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
        FStar_Util.bind_opt uu___1
          (fun l1 ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Reflectable l1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (l, uu___)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
        ->
        let uu___1 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
        FStar_Util.bind_opt uu___1
          (fun l1 ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Discriminator l1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (l, uu___)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
        ->
        let uu___1 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
        FStar_Util.bind_opt uu___1
          (fun l1 ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Action l1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, [], (i, uu___)::(l, uu___1)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
        ->
        let uu___2 = FStar_TypeChecker_NBETerm.unembed e_ident cb i in
        FStar_Util.bind_opt uu___2
          (fun i1 ->
             let uu___3 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
             FStar_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Projector (l1, i1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, [], (ids2, uu___)::(ids1, uu___1)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
        ->
        let uu___2 =
          let uu___3 = FStar_TypeChecker_NBETerm.e_list e_ident in
          FStar_TypeChecker_NBETerm.unembed uu___3 cb ids1 in
        FStar_Util.bind_opt uu___2
          (fun ids11 ->
             let uu___3 =
               let uu___4 = FStar_TypeChecker_NBETerm.e_list e_ident in
               FStar_TypeChecker_NBETerm.unembed uu___4 cb ids2 in
             FStar_Util.bind_opt uu___3
               (fun ids21 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordType (ids11, ids21))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, [], (ids2, uu___)::(ids1, uu___1)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
        ->
        let uu___2 =
          let uu___3 = FStar_TypeChecker_NBETerm.e_list e_ident in
          FStar_TypeChecker_NBETerm.unembed uu___3 cb ids1 in
        FStar_Util.bind_opt uu___2
          (fun ids11 ->
             let uu___3 =
               let uu___4 = FStar_TypeChecker_NBETerm.e_list e_ident in
               FStar_TypeChecker_NBETerm.unembed uu___4 cb ids2 in
             FStar_Util.bind_opt uu___3
               (fun ids21 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordConstructor (ids11, ids21))))
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded qualifier: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  let uu___ = mkConstruct FStar_Reflection_Data.fstar_refl_qualifier_fv [] [] in
  let uu___1 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_qualifier_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed unembed uu___ uu___1
let (e_qualifiers :
  FStar_Reflection_Data.qualifier Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_qualifier
let (e_vconfig : FStar_Order.order FStar_TypeChecker_NBETerm.embedding) =
  let emb cb o = failwith "emb vconfig NBE" in
  let unemb cb t = failwith "unemb vconfig NBE" in
  let uu___ =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.vconfig_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  mk_emb' emb unemb uu___