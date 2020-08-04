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
    let uu____75 =
      let uu____82 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      (uu____82, []) in
    FStar_Syntax_Syntax.ET_app uu____75
let mk_emb' :
  'uuuuuu93 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'uuuuuu93 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'uuuuuu93 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'uuuuuu93 FStar_TypeChecker_NBETerm.embedding
  =
  fun x ->
    fun y ->
      fun fv ->
        let uu____135 = mkFV fv [] [] in
        let uu____140 = fv_as_emb_typ fv in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____135 uu____140
let mk_lazy :
  'uuuuuu151 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'uuuuuu151 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb ->
    fun obj ->
      fun ty ->
        fun kind ->
          let li =
            let uu____177 = FStar_Dyn.mkdyn obj in
            {
              FStar_Syntax_Syntax.blob = uu____177;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            } in
          let thunk =
            FStar_Thunk.mk
              (fun uu____183 ->
                 let uu____184 = FStar_Syntax_Util.unfold_lazy li in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____184) in
          FStar_TypeChecker_NBETerm.mk_t
            (FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk))
let (e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv cb bv =
    mk_lazy cb bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv in
  let unembed_bv cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv;
           FStar_Syntax_Syntax.ltyp = uu____228;
           FStar_Syntax_Syntax.rng = uu____229;_},
         uu____230)
        ->
        let uu____249 = FStar_Dyn.undyn b in
        FStar_All.pipe_left
          (fun uu____252 -> FStar_Pervasives_Native.Some uu____252) uu____249
    | uu____253 ->
        ((let uu____255 =
            let uu____260 =
              let uu____261 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded bv: %s" uu____261 in
            (FStar_Errors.Warning_NotEmbedded, uu____260) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____255);
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
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder;
           FStar_Syntax_Syntax.ltyp = uu____291;
           FStar_Syntax_Syntax.rng = uu____292;_},
         uu____293)
        ->
        let uu____312 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____312
    | uu____313 ->
        ((let uu____315 =
            let uu____320 =
              let uu____321 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded binder: %s" uu____321 in
            (FStar_Errors.Warning_NotEmbedded, uu____320) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____315);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_binder unembed_binder
    FStar_Reflection_Data.fstar_refl_binder_fv
let (e_optionstate :
  FStar_Options.optionstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_optionstate cb b =
    mk_lazy cb b FStar_Reflection_Data.fstar_refl_optionstate
      FStar_Syntax_Syntax.Lazy_optionstate in
  let unembed_optionstate cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_optionstate;
           FStar_Syntax_Syntax.ltyp = uu____351;
           FStar_Syntax_Syntax.rng = uu____352;_},
         uu____353)
        ->
        let uu____372 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____372
    | uu____373 ->
        ((let uu____375 =
            let uu____380 =
              let uu____381 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded optionstate: %s" uu____381 in
            (FStar_Errors.Warning_NotEmbedded, uu____380) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____375);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_optionstate unembed_optionstate
    FStar_Reflection_Data.fstar_refl_optionstate_fv
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
          let uu____427 = f x in
          FStar_Util.bind_opt uu____427
            (fun x1 ->
               let uu____435 = mapM_opt f xs in
               FStar_Util.bind_opt uu____435
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
      | uu____504 -> FStar_Pervasives_Native.None in
    let uu____505 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] [] in
    let uu____510 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____505;
      FStar_TypeChecker_NBETerm.emb_typ = uu____510
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
        let uu____541 =
          let uu____548 =
            let uu____553 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu____553 in
          [uu____548] in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____541
    | FStar_Reflection_Data.Q_Meta_attr t ->
        let uu____563 =
          let uu____570 =
            let uu____575 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu____575 in
          [uu____570] in
        mkConstruct
          FStar_Reflection_Data.ref_Q_Meta_attr.FStar_Reflection_Data.fv []
          uu____563 in
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
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (t1, uu____627)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____644 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu____644
          (fun t2 ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (t1, uu____651)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta_attr.FStar_Reflection_Data.lid
        ->
        let uu____668 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu____668
          (fun t2 ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Q_Meta_attr t2))
    | uu____673 ->
        ((let uu____675 =
            let uu____680 =
              let uu____681 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____681 in
            (FStar_Errors.Warning_NotEmbedded, uu____680) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____675);
         FStar_Pervasives_Native.None) in
  let uu____682 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] [] in
  let uu____687 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____682
    uu____687
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
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar;
           FStar_Syntax_Syntax.ltyp = uu____719;
           FStar_Syntax_Syntax.rng = uu____720;_},
         uu____721)
        ->
        let uu____740 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____740
    | uu____741 ->
        ((let uu____743 =
            let uu____748 =
              let uu____749 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____749 in
            (FStar_Errors.Warning_NotEmbedded, uu____748) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____743);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv_fv
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp cb c =
    mk_lazy cb c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp in
  let unembed_comp cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp;
           FStar_Syntax_Syntax.ltyp = uu____779;
           FStar_Syntax_Syntax.rng = uu____780;_},
         uu____781)
        ->
        let uu____800 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____800
    | uu____801 ->
        ((let uu____803 =
            let uu____808 =
              let uu____809 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded comp: %s" uu____809 in
            (FStar_Errors.Warning_NotEmbedded, uu____808) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____803);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp_fv
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env cb e =
    mk_lazy cb e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env in
  let unembed_env cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env;
           FStar_Syntax_Syntax.ltyp = uu____839;
           FStar_Syntax_Syntax.rng = uu____840;_},
         uu____841)
        ->
        let uu____860 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____860
    | uu____861 ->
        ((let uu____863 =
            let uu____868 =
              let uu____869 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded env: %s" uu____869 in
            (FStar_Errors.Warning_NotEmbedded, uu____868) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____863);
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
        let uu____896 =
          let uu____903 =
            let uu____908 =
              FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
                (FStar_TypeChecker_NBETerm.Constant
                   (FStar_TypeChecker_NBETerm.Int i)) in
            FStar_TypeChecker_NBETerm.as_arg uu____908 in
          [uu____903] in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____896
    | FStar_Reflection_Data.C_String s ->
        let uu____918 =
          let uu____925 =
            let uu____930 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s in
            FStar_TypeChecker_NBETerm.as_arg uu____930 in
          [uu____925] in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____918
    | FStar_Reflection_Data.C_Range r ->
        let uu____940 =
          let uu____947 =
            let uu____952 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r in
            FStar_TypeChecker_NBETerm.as_arg uu____952 in
          [uu____947] in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____940
    | FStar_Reflection_Data.C_Reify ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____966 =
          let uu____973 =
            let uu____978 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns in
            FStar_TypeChecker_NBETerm.as_arg uu____978 in
          [uu____973] in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____966 in
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
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (i, uu____1045)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____1062 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i in
        FStar_Util.bind_opt uu____1062
          (fun i1 ->
             FStar_All.pipe_left
               (fun uu____1069 -> FStar_Pervasives_Native.Some uu____1069)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (s, uu____1072)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____1089 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s in
        FStar_Util.bind_opt uu____1089
          (fun s1 ->
             FStar_All.pipe_left
               (fun uu____1096 -> FStar_Pervasives_Native.Some uu____1096)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (r, uu____1099)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____1116 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r in
        FStar_Util.bind_opt uu____1116
          (fun r1 ->
             FStar_All.pipe_left
               (fun uu____1123 -> FStar_Pervasives_Native.Some uu____1123)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (ns, uu____1139)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____1156 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns in
        FStar_Util.bind_opt uu____1156
          (fun ns1 ->
             FStar_All.pipe_left
               (fun uu____1171 -> FStar_Pervasives_Native.Some uu____1171)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____1172 ->
        ((let uu____1174 =
            let uu____1179 =
              let uu____1180 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____1180 in
            (FStar_Errors.Warning_NotEmbedded, uu____1179) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1174);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____1187 ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1200 =
            let uu____1207 =
              let uu____1212 = FStar_TypeChecker_NBETerm.embed e_const cb c in
              FStar_TypeChecker_NBETerm.as_arg uu____1212 in
            [uu____1207] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____1200
      | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
          let uu____1235 =
            let uu____1242 =
              let uu____1247 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu____1247 in
            let uu____1248 =
              let uu____1255 =
                let uu____1260 =
                  let uu____1261 =
                    let uu____1270 =
                      let uu____1277 = e_pattern' () in
                      FStar_TypeChecker_NBETerm.e_tuple2 uu____1277
                        FStar_TypeChecker_NBETerm.e_bool in
                    FStar_TypeChecker_NBETerm.e_list uu____1270 in
                  FStar_TypeChecker_NBETerm.embed uu____1261 cb ps in
                FStar_TypeChecker_NBETerm.as_arg uu____1260 in
              [uu____1255] in
            uu____1242 :: uu____1248 in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1235
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1303 =
            let uu____1310 =
              let uu____1315 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1315 in
            [uu____1310] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1303
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1325 =
            let uu____1332 =
              let uu____1337 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1337 in
            [uu____1332] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1325
      | FStar_Reflection_Data.Pat_Dot_Term (bv, t) ->
          let uu____1348 =
            let uu____1355 =
              let uu____1360 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1360 in
            let uu____1361 =
              let uu____1368 =
                let uu____1373 = FStar_TypeChecker_NBETerm.embed e_term cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____1373 in
              [uu____1368] in
            uu____1355 :: uu____1361 in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1348 in
    let unembed_pattern cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (c, uu____1403)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1420 = FStar_TypeChecker_NBETerm.unembed e_const cb c in
          FStar_Util.bind_opt uu____1420
            (fun c1 ->
               FStar_All.pipe_left
                 (fun uu____1427 -> FStar_Pervasives_Native.Some uu____1427)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, [], (ps, uu____1430)::(f, uu____1432)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1453 = FStar_TypeChecker_NBETerm.unembed e_fv cb f in
          FStar_Util.bind_opt uu____1453
            (fun f1 ->
               let uu____1459 =
                 let uu____1468 =
                   let uu____1477 =
                     let uu____1484 = e_pattern' () in
                     FStar_TypeChecker_NBETerm.e_tuple2 uu____1484
                       FStar_TypeChecker_NBETerm.e_bool in
                   FStar_TypeChecker_NBETerm.e_list uu____1477 in
                 FStar_TypeChecker_NBETerm.unembed uu____1468 cb ps in
               FStar_Util.bind_opt uu____1459
                 (fun ps1 ->
                    FStar_All.pipe_left
                      (fun uu____1513 ->
                         FStar_Pervasives_Native.Some uu____1513)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (bv, uu____1522)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1539 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu____1539
            (fun bv1 ->
               FStar_All.pipe_left
                 (fun uu____1546 -> FStar_Pervasives_Native.Some uu____1546)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (bv, uu____1549)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1566 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu____1566
            (fun bv1 ->
               FStar_All.pipe_left
                 (fun uu____1573 -> FStar_Pervasives_Native.Some uu____1573)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, [], (t1, uu____1576)::(bv, uu____1578)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1599 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu____1599
            (fun bv1 ->
               let uu____1605 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____1605
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun uu____1612 ->
                         FStar_Pervasives_Native.Some uu____1612)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1613 ->
          ((let uu____1615 =
              let uu____1620 =
                let uu____1621 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1621 in
              (FStar_Errors.Warning_NotEmbedded, uu____1620) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1615);
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
    let uu____1655 = e_term_aq aq in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1655
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let uu____1685 = e_term_aq aq in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1685 e_aqualv
let unlazy_as_t :
  'uuuuuu1694 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'uuuuuu1694
  =
  fun k ->
    fun t ->
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____1707;
             FStar_Syntax_Syntax.rng = uu____1708;_},
           uu____1709)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____1728 -> failwith "Not a Lazy of the expected kind (NBE)"
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1764 =
            let uu____1771 =
              let uu____1776 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu____1776 in
            [uu____1771] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1764
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1786 =
            let uu____1793 =
              let uu____1798 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1798 in
            [uu____1793] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1786
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1808 =
            let uu____1815 =
              let uu____1820 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1820 in
            [uu____1815] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1808
      | FStar_Reflection_Data.Tv_App (hd, a) ->
          let uu____1831 =
            let uu____1838 =
              let uu____1843 =
                let uu____1844 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____1844 cb hd in
              FStar_TypeChecker_NBETerm.as_arg uu____1843 in
            let uu____1847 =
              let uu____1854 =
                let uu____1859 =
                  let uu____1860 = e_argv_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____1860 cb a in
                FStar_TypeChecker_NBETerm.as_arg uu____1859 in
              [uu____1854] in
            uu____1838 :: uu____1847 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1831
      | FStar_Reflection_Data.Tv_Abs (b, t) ->
          let uu____1885 =
            let uu____1892 =
              let uu____1897 = FStar_TypeChecker_NBETerm.embed e_binder cb b in
              FStar_TypeChecker_NBETerm.as_arg uu____1897 in
            let uu____1898 =
              let uu____1905 =
                let uu____1910 =
                  let uu____1911 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____1911 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____1910 in
              [uu____1905] in
            uu____1892 :: uu____1898 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1885
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          let uu____1928 =
            let uu____1935 =
              let uu____1940 = FStar_TypeChecker_NBETerm.embed e_binder cb b in
              FStar_TypeChecker_NBETerm.as_arg uu____1940 in
            let uu____1941 =
              let uu____1948 =
                let uu____1953 = FStar_TypeChecker_NBETerm.embed e_comp cb c in
                FStar_TypeChecker_NBETerm.as_arg uu____1953 in
              [uu____1948] in
            uu____1935 :: uu____1941 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1928
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1967 =
            let uu____1974 =
              let uu____1979 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb () in
              FStar_TypeChecker_NBETerm.as_arg uu____1979 in
            [uu____1974] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1967
      | FStar_Reflection_Data.Tv_Refine (bv, t) ->
          let uu____1990 =
            let uu____1997 =
              let uu____2002 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____2002 in
            let uu____2003 =
              let uu____2010 =
                let uu____2015 =
                  let uu____2016 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____2016 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____2015 in
              [uu____2010] in
            uu____1997 :: uu____2003 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1990
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2032 =
            let uu____2039 =
              let uu____2044 = FStar_TypeChecker_NBETerm.embed e_const cb c in
              FStar_TypeChecker_NBETerm.as_arg uu____2044 in
            [uu____2039] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____2032
      | FStar_Reflection_Data.Tv_Uvar (u, d) ->
          let uu____2055 =
            let uu____2062 =
              let uu____2067 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u in
              FStar_TypeChecker_NBETerm.as_arg uu____2067 in
            let uu____2068 =
              let uu____2075 =
                let uu____2080 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar in
                FStar_TypeChecker_NBETerm.as_arg uu____2080 in
              [uu____2075] in
            uu____2062 :: uu____2068 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____2055
      | FStar_Reflection_Data.Tv_Let (r, attrs, b, t1, t2) ->
          let uu____2106 =
            let uu____2113 =
              let uu____2118 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r in
              FStar_TypeChecker_NBETerm.as_arg uu____2118 in
            let uu____2119 =
              let uu____2126 =
                let uu____2131 =
                  let uu____2132 = FStar_TypeChecker_NBETerm.e_list e_term in
                  FStar_TypeChecker_NBETerm.embed uu____2132 cb attrs in
                FStar_TypeChecker_NBETerm.as_arg uu____2131 in
              let uu____2139 =
                let uu____2146 =
                  let uu____2151 = FStar_TypeChecker_NBETerm.embed e_bv cb b in
                  FStar_TypeChecker_NBETerm.as_arg uu____2151 in
                let uu____2152 =
                  let uu____2159 =
                    let uu____2164 =
                      let uu____2165 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.embed uu____2165 cb t1 in
                    FStar_TypeChecker_NBETerm.as_arg uu____2164 in
                  let uu____2168 =
                    let uu____2175 =
                      let uu____2180 =
                        let uu____2181 = e_term_aq aq in
                        FStar_TypeChecker_NBETerm.embed uu____2181 cb t2 in
                      FStar_TypeChecker_NBETerm.as_arg uu____2180 in
                    [uu____2175] in
                  uu____2159 :: uu____2168 in
                uu____2146 :: uu____2152 in
              uu____2126 :: uu____2139 in
            uu____2113 :: uu____2119 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____2106
      | FStar_Reflection_Data.Tv_Match (t, brs) ->
          let uu____2214 =
            let uu____2221 =
              let uu____2226 =
                let uu____2227 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____2227 cb t in
              FStar_TypeChecker_NBETerm.as_arg uu____2226 in
            let uu____2230 =
              let uu____2237 =
                let uu____2242 =
                  let uu____2243 =
                    let uu____2252 = e_branch_aq aq in
                    FStar_TypeChecker_NBETerm.e_list uu____2252 in
                  FStar_TypeChecker_NBETerm.embed uu____2243 cb brs in
                FStar_TypeChecker_NBETerm.as_arg uu____2242 in
              [uu____2237] in
            uu____2221 :: uu____2230 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2214
      | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
          let uu____2288 =
            let uu____2295 =
              let uu____2300 =
                let uu____2301 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____2301 cb e in
              FStar_TypeChecker_NBETerm.as_arg uu____2300 in
            let uu____2304 =
              let uu____2311 =
                let uu____2316 =
                  let uu____2317 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____2317 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____2316 in
              let uu____2320 =
                let uu____2327 =
                  let uu____2332 =
                    let uu____2333 =
                      let uu____2338 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.e_option uu____2338 in
                    FStar_TypeChecker_NBETerm.embed uu____2333 cb tacopt in
                  FStar_TypeChecker_NBETerm.as_arg uu____2332 in
                [uu____2327] in
              uu____2311 :: uu____2320 in
            uu____2295 :: uu____2304 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2288
      | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
          let uu____2366 =
            let uu____2373 =
              let uu____2378 =
                let uu____2379 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____2379 cb e in
              FStar_TypeChecker_NBETerm.as_arg uu____2378 in
            let uu____2382 =
              let uu____2389 =
                let uu____2394 = FStar_TypeChecker_NBETerm.embed e_comp cb c in
                FStar_TypeChecker_NBETerm.as_arg uu____2394 in
              let uu____2395 =
                let uu____2402 =
                  let uu____2407 =
                    let uu____2408 =
                      let uu____2413 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.e_option uu____2413 in
                    FStar_TypeChecker_NBETerm.embed uu____2408 cb tacopt in
                  FStar_TypeChecker_NBETerm.as_arg uu____2407 in
                [uu____2402] in
              uu____2389 :: uu____2395 in
            uu____2373 :: uu____2382 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2366
      | FStar_Reflection_Data.Tv_Unknown ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            [] in
    let unembed_term_view cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2454, (b, uu____2456)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2475 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu____2475
            (fun b1 ->
               FStar_All.pipe_left
                 (fun uu____2482 -> FStar_Pervasives_Native.Some uu____2482)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2484, (b, uu____2486)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2505 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu____2505
            (fun b1 ->
               FStar_All.pipe_left
                 (fun uu____2512 -> FStar_Pervasives_Native.Some uu____2512)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2514, (f, uu____2516)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2535 = FStar_TypeChecker_NBETerm.unembed e_fv cb f in
          FStar_Util.bind_opt uu____2535
            (fun f1 ->
               FStar_All.pipe_left
                 (fun uu____2542 -> FStar_Pervasives_Native.Some uu____2542)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2544, (r, uu____2546)::(l, uu____2548)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2571 = FStar_TypeChecker_NBETerm.unembed e_term cb l in
          FStar_Util.bind_opt uu____2571
            (fun l1 ->
               let uu____2577 = FStar_TypeChecker_NBETerm.unembed e_argv cb r in
               FStar_Util.bind_opt uu____2577
                 (fun r1 ->
                    FStar_All.pipe_left
                      (fun uu____2584 ->
                         FStar_Pervasives_Native.Some uu____2584)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2586, (t1, uu____2588)::(b, uu____2590)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2613 = FStar_TypeChecker_NBETerm.unembed e_binder cb b in
          FStar_Util.bind_opt uu____2613
            (fun b1 ->
               let uu____2619 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____2619
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun uu____2626 ->
                         FStar_Pervasives_Native.Some uu____2626)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2628, (t1, uu____2630)::(b, uu____2632)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2655 = FStar_TypeChecker_NBETerm.unembed e_binder cb b in
          FStar_Util.bind_opt uu____2655
            (fun b1 ->
               let uu____2661 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1 in
               FStar_Util.bind_opt uu____2661
                 (fun c ->
                    FStar_All.pipe_left
                      (fun uu____2668 ->
                         FStar_Pervasives_Native.Some uu____2668)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2670, (u, uu____2672)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2691 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u in
          FStar_Util.bind_opt uu____2691
            (fun u1 ->
               FStar_All.pipe_left
                 (fun uu____2698 -> FStar_Pervasives_Native.Some uu____2698)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2700, (t1, uu____2702)::(b, uu____2704)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2727 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu____2727
            (fun b1 ->
               let uu____2733 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____2733
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun uu____2740 ->
                         FStar_Pervasives_Native.Some uu____2740)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2742, (c, uu____2744)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2763 = FStar_TypeChecker_NBETerm.unembed e_const cb c in
          FStar_Util.bind_opt uu____2763
            (fun c1 ->
               FStar_All.pipe_left
                 (fun uu____2770 -> FStar_Pervasives_Native.Some uu____2770)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2772, (l, uu____2774)::(u, uu____2776)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2799 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u in
          FStar_Util.bind_opt uu____2799
            (fun u1 ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l in
               FStar_All.pipe_left
                 (fun uu____2808 -> FStar_Pervasives_Native.Some uu____2808)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2810,
           (t2, uu____2812)::(t1, uu____2814)::(b, uu____2816)::(attrs,
                                                                 uu____2818)::
           (r, uu____2820)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2855 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r in
          FStar_Util.bind_opt uu____2855
            (fun r1 ->
               let uu____2861 =
                 let uu____2866 = FStar_TypeChecker_NBETerm.e_list e_term in
                 FStar_TypeChecker_NBETerm.unembed uu____2866 cb attrs in
               FStar_Util.bind_opt uu____2861
                 (fun attrs1 ->
                    let uu____2880 =
                      FStar_TypeChecker_NBETerm.unembed e_bv cb b in
                    FStar_Util.bind_opt uu____2880
                      (fun b1 ->
                         let uu____2886 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                         FStar_Util.bind_opt uu____2886
                           (fun t11 ->
                              let uu____2892 =
                                FStar_TypeChecker_NBETerm.unembed e_term cb
                                  t2 in
                              FStar_Util.bind_opt uu____2892
                                (fun t21 ->
                                   FStar_All.pipe_left
                                     (fun uu____2899 ->
                                        FStar_Pervasives_Native.Some
                                          uu____2899)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, attrs1, b1, t11, t21)))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2903, (brs, uu____2905)::(t1, uu____2907)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2930 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
          FStar_Util.bind_opt uu____2930
            (fun t2 ->
               let uu____2936 =
                 let uu____2941 = FStar_TypeChecker_NBETerm.e_list e_branch in
                 FStar_TypeChecker_NBETerm.unembed uu____2941 cb brs in
               FStar_Util.bind_opt uu____2936
                 (fun brs1 ->
                    FStar_All.pipe_left
                      (fun uu____2956 ->
                         FStar_Pervasives_Native.Some uu____2956)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2960,
           (tacopt, uu____2962)::(t1, uu____2964)::(e, uu____2966)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2993 = FStar_TypeChecker_NBETerm.unembed e_term cb e in
          FStar_Util.bind_opt uu____2993
            (fun e1 ->
               let uu____2999 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____2999
                 (fun t2 ->
                    let uu____3005 =
                      let uu____3010 =
                        FStar_TypeChecker_NBETerm.e_option e_term in
                      FStar_TypeChecker_NBETerm.unembed uu____3010 cb tacopt in
                    FStar_Util.bind_opt uu____3005
                      (fun tacopt1 ->
                         FStar_All.pipe_left
                           (fun uu____3025 ->
                              FStar_Pervasives_Native.Some uu____3025)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____3029,
           (tacopt, uu____3031)::(c, uu____3033)::(e, uu____3035)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____3062 = FStar_TypeChecker_NBETerm.unembed e_term cb e in
          FStar_Util.bind_opt uu____3062
            (fun e1 ->
               let uu____3068 = FStar_TypeChecker_NBETerm.unembed e_comp cb c in
               FStar_Util.bind_opt uu____3068
                 (fun c1 ->
                    let uu____3074 =
                      let uu____3079 =
                        FStar_TypeChecker_NBETerm.e_option e_term in
                      FStar_TypeChecker_NBETerm.unembed uu____3079 cb tacopt in
                    FStar_Util.bind_opt uu____3074
                      (fun tacopt1 ->
                         FStar_All.pipe_left
                           (fun uu____3094 ->
                              FStar_Pervasives_Native.Some uu____3094)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv, uu____3098, []) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun uu____3115 -> FStar_Pervasives_Native.Some uu____3115)
            FStar_Reflection_Data.Tv_Unknown
      | uu____3116 ->
          ((let uu____3118 =
              let uu____3123 =
                let uu____3124 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____3124 in
              (FStar_Errors.Warning_NotEmbedded, uu____3123) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3118);
           FStar_Pervasives_Native.None) in
    mk_emb' embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view_fv
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq []
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view cb bvv =
    let uu____3146 =
      let uu____3153 =
        let uu____3158 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname in
        FStar_TypeChecker_NBETerm.as_arg uu____3158 in
      let uu____3159 =
        let uu____3166 =
          let uu____3171 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index in
          FStar_TypeChecker_NBETerm.as_arg uu____3171 in
        let uu____3172 =
          let uu____3179 =
            let uu____3184 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort in
            FStar_TypeChecker_NBETerm.as_arg uu____3184 in
          [uu____3179] in
        uu____3166 :: uu____3172 in
      uu____3153 :: uu____3159 in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____3146 in
  let unembed_bv_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3217,
         (s, uu____3219)::(idx, uu____3221)::(nm, uu____3223)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____3250 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm in
        FStar_Util.bind_opt uu____3250
          (fun nm1 ->
             let uu____3256 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx in
             FStar_Util.bind_opt uu____3256
               (fun idx1 ->
                  let uu____3262 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s in
                  FStar_Util.bind_opt uu____3262
                    (fun s1 ->
                       FStar_All.pipe_left
                         (fun uu____3269 ->
                            FStar_Pervasives_Native.Some uu____3269)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____3270 ->
        ((let uu____3272 =
            let uu____3277 =
              let uu____3278 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3278 in
            (FStar_Errors.Warning_NotEmbedded, uu____3277) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3272);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t, md) ->
        let uu____3298 =
          let uu____3305 =
            let uu____3310 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu____3310 in
          let uu____3311 =
            let uu____3318 =
              let uu____3323 =
                let uu____3324 = FStar_TypeChecker_NBETerm.e_option e_term in
                FStar_TypeChecker_NBETerm.embed uu____3324 cb md in
              FStar_TypeChecker_NBETerm.as_arg uu____3323 in
            [uu____3318] in
          uu____3305 :: uu____3311 in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3298
    | FStar_Reflection_Data.C_GTotal (t, md) ->
        let uu____3349 =
          let uu____3356 =
            let uu____3361 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu____3361 in
          let uu____3362 =
            let uu____3369 =
              let uu____3374 =
                let uu____3375 = FStar_TypeChecker_NBETerm.e_option e_term in
                FStar_TypeChecker_NBETerm.embed uu____3375 cb md in
              FStar_TypeChecker_NBETerm.as_arg uu____3374 in
            [uu____3369] in
          uu____3356 :: uu____3362 in
        mkConstruct
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.fv []
          uu____3349
    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
        let uu____3397 =
          let uu____3404 =
            let uu____3409 = FStar_TypeChecker_NBETerm.embed e_term cb pre in
            FStar_TypeChecker_NBETerm.as_arg uu____3409 in
          let uu____3410 =
            let uu____3417 =
              let uu____3422 = FStar_TypeChecker_NBETerm.embed e_term cb post in
              FStar_TypeChecker_NBETerm.as_arg uu____3422 in
            let uu____3423 =
              let uu____3430 =
                let uu____3435 =
                  FStar_TypeChecker_NBETerm.embed e_term cb pats in
                FStar_TypeChecker_NBETerm.as_arg uu____3435 in
              [uu____3430] in
            uu____3417 :: uu____3423 in
          uu____3404 :: uu____3410 in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3397
    | FStar_Reflection_Data.C_Eff (us, eff, res, args) ->
        let uu____3464 =
          let uu____3471 =
            let uu____3476 =
              let uu____3477 =
                FStar_TypeChecker_NBETerm.e_list
                  FStar_TypeChecker_NBETerm.e_unit in
              FStar_TypeChecker_NBETerm.embed uu____3477 cb us in
            FStar_TypeChecker_NBETerm.as_arg uu____3476 in
          let uu____3484 =
            let uu____3491 =
              let uu____3496 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_string_list cb eff in
              FStar_TypeChecker_NBETerm.as_arg uu____3496 in
            let uu____3499 =
              let uu____3506 =
                let uu____3511 =
                  FStar_TypeChecker_NBETerm.embed e_term cb res in
                FStar_TypeChecker_NBETerm.as_arg uu____3511 in
              let uu____3512 =
                let uu____3519 =
                  let uu____3524 =
                    let uu____3525 = FStar_TypeChecker_NBETerm.e_list e_argv in
                    FStar_TypeChecker_NBETerm.embed uu____3525 cb args in
                  FStar_TypeChecker_NBETerm.as_arg uu____3524 in
                [uu____3519] in
              uu____3506 :: uu____3512 in
            uu____3491 :: uu____3499 in
          uu____3471 :: uu____3484 in
        mkConstruct FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.fv
          [] uu____3464 in
  let unembed_comp_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3568, (md, uu____3570)::(t1, uu____3572)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3595 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu____3595
          (fun t2 ->
             let uu____3601 =
               let uu____3606 = FStar_TypeChecker_NBETerm.e_option e_term in
               FStar_TypeChecker_NBETerm.unembed uu____3606 cb md in
             FStar_Util.bind_opt uu____3601
               (fun md1 ->
                  FStar_All.pipe_left
                    (fun uu____3621 ->
                       FStar_Pervasives_Native.Some uu____3621)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3625, (md, uu____3627)::(t1, uu____3629)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
        ->
        let uu____3652 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu____3652
          (fun t2 ->
             let uu____3658 =
               let uu____3663 = FStar_TypeChecker_NBETerm.e_option e_term in
               FStar_TypeChecker_NBETerm.unembed uu____3663 cb md in
             FStar_Util.bind_opt uu____3658
               (fun md1 ->
                  FStar_All.pipe_left
                    (fun uu____3678 ->
                       FStar_Pervasives_Native.Some uu____3678)
                    (FStar_Reflection_Data.C_GTotal (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3682,
         (post, uu____3684)::(pre, uu____3686)::(pats, uu____3688)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3715 = FStar_TypeChecker_NBETerm.unembed e_term cb pre in
        FStar_Util.bind_opt uu____3715
          (fun pre1 ->
             let uu____3721 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post in
             FStar_Util.bind_opt uu____3721
               (fun post1 ->
                  let uu____3727 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb pats in
                  FStar_Util.bind_opt uu____3727
                    (fun pats1 ->
                       FStar_All.pipe_left
                         (fun uu____3734 ->
                            FStar_Pervasives_Native.Some uu____3734)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1, pats1)))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3736,
         (args, uu____3738)::(res, uu____3740)::(eff, uu____3742)::(us,
                                                                    uu____3744)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
        ->
        let uu____3775 =
          let uu____3780 =
            FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_unit in
          FStar_TypeChecker_NBETerm.unembed uu____3780 cb us in
        FStar_Util.bind_opt uu____3775
          (fun us1 ->
             let uu____3794 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_string_list cb eff in
             FStar_Util.bind_opt uu____3794
               (fun eff1 ->
                  let uu____3808 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb res in
                  FStar_Util.bind_opt uu____3808
                    (fun res1 ->
                       let uu____3814 =
                         let uu____3819 =
                           FStar_TypeChecker_NBETerm.e_list e_argv in
                         FStar_TypeChecker_NBETerm.unembed uu____3819 cb args in
                       FStar_Util.bind_opt uu____3814
                         (fun args1 ->
                            FStar_All.pipe_left
                              (fun uu____3834 ->
                                 FStar_Pervasives_Native.Some uu____3834)
                              (FStar_Reflection_Data.C_Eff
                                 (us1, eff1, res1, args1))))))
    | uu____3839 ->
        ((let uu____3841 =
            let uu____3846 =
              let uu____3847 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3847 in
            (FStar_Errors.Warning_NotEmbedded, uu____3846) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3841);
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
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3889, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3905, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3921, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____3936 ->
        ((let uu____3938 =
            let uu____3943 =
              let uu____3944 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded order: %s" uu____3944 in
            (FStar_Errors.Warning_NotEmbedded, uu____3943) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3938);
         FStar_Pervasives_Native.None) in
  let uu____3945 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  mk_emb' embed_order unembed_order uu____3945
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt cb se =
    mk_lazy cb se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt in
  let unembed_sigelt cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt;
           FStar_Syntax_Syntax.ltyp = uu____3975;
           FStar_Syntax_Syntax.rng = uu____3976;_},
         uu____3977)
        ->
        let uu____3996 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____3996
    | uu____3997 ->
        ((let uu____3999 =
            let uu____4004 =
              let uu____4005 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____4005 in
            (FStar_Errors.Warning_NotEmbedded, uu____4004) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3999);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt_fv
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string in
  let embed_ident cb i =
    let uu____4028 =
      let uu____4033 = FStar_Ident.range_of_id i in
      let uu____4034 = FStar_Ident.string_of_id i in (uu____4033, uu____4034) in
    FStar_TypeChecker_NBETerm.embed repr cb uu____4028 in
  let unembed_ident cb t =
    let uu____4054 = FStar_TypeChecker_NBETerm.unembed repr cb t in
    match uu____4054 with
    | FStar_Pervasives_Native.Some (rng, s) ->
        let uu____4073 = FStar_Ident.mk_ident (s, rng) in
        FStar_Pervasives_Native.Some uu____4073
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let range_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  let string_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  let et =
    let uu____4081 =
      let uu____4088 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2 in
      let uu____4089 =
        let uu____4092 = fv_as_emb_typ range_fv in
        let uu____4093 =
          let uu____4096 = fv_as_emb_typ string_fv in [uu____4096] in
        uu____4092 :: uu____4093 in
      (uu____4088, uu____4089) in
    FStar_Syntax_Syntax.ET_app uu____4081 in
  let uu____4099 =
    let uu____4100 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    let uu____4101 =
      let uu____4108 =
        let uu____4113 = mkFV range_fv [] [] in
        FStar_TypeChecker_NBETerm.as_arg uu____4113 in
      let uu____4118 =
        let uu____4125 =
          let uu____4130 = mkFV string_fv [] [] in
          FStar_TypeChecker_NBETerm.as_arg uu____4130 in
        [uu____4125] in
      uu____4108 :: uu____4118 in
    mkFV uu____4100 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____4101 in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____4099 et
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
        let uu____4189 =
          let uu____4196 =
            let uu____4201 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r in
            FStar_TypeChecker_NBETerm.as_arg uu____4201 in
          let uu____4202 =
            let uu____4209 =
              let uu____4214 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu____4214 in
            let uu____4215 =
              let uu____4222 =
                let uu____4227 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs in
                FStar_TypeChecker_NBETerm.as_arg uu____4227 in
              let uu____4230 =
                let uu____4237 =
                  let uu____4242 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty in
                  FStar_TypeChecker_NBETerm.as_arg uu____4242 in
                let uu____4243 =
                  let uu____4250 =
                    let uu____4255 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t in
                    FStar_TypeChecker_NBETerm.as_arg uu____4255 in
                  [uu____4250] in
                uu____4237 :: uu____4243 in
              uu____4222 :: uu____4230 in
            uu____4209 :: uu____4215 in
          uu____4196 :: uu____4202 in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____4189
    | FStar_Reflection_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu____4297 =
          let uu____4304 =
            let uu____4309 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm in
            FStar_TypeChecker_NBETerm.as_arg uu____4309 in
          let uu____4312 =
            let uu____4319 =
              let uu____4324 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs in
              FStar_TypeChecker_NBETerm.as_arg uu____4324 in
            let uu____4327 =
              let uu____4334 =
                let uu____4339 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs in
                FStar_TypeChecker_NBETerm.as_arg uu____4339 in
              let uu____4340 =
                let uu____4347 =
                  let uu____4352 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t in
                  FStar_TypeChecker_NBETerm.as_arg uu____4352 in
                let uu____4353 =
                  let uu____4360 =
                    let uu____4365 =
                      let uu____4366 =
                        FStar_TypeChecker_NBETerm.e_list e_ctor in
                      FStar_TypeChecker_NBETerm.embed uu____4366 cb dcs in
                    FStar_TypeChecker_NBETerm.as_arg uu____4365 in
                  [uu____4360] in
                uu____4347 :: uu____4353 in
              uu____4334 :: uu____4340 in
            uu____4319 :: uu____4327 in
          uu____4304 :: uu____4312 in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____4297
    | FStar_Reflection_Data.Unk ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          [] in
  let unembed_sigelt_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4435,
         (dcs, uu____4437)::(t1, uu____4439)::(bs, uu____4441)::(us,
                                                                 uu____4443)::
         (nm, uu____4445)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____4480 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm in
        FStar_Util.bind_opt uu____4480
          (fun nm1 ->
             let uu____4494 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us in
             FStar_Util.bind_opt uu____4494
               (fun us1 ->
                  let uu____4508 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs in
                  FStar_Util.bind_opt uu____4508
                    (fun bs1 ->
                       let uu____4514 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                       FStar_Util.bind_opt uu____4514
                         (fun t2 ->
                            let uu____4520 =
                              let uu____4531 =
                                FStar_TypeChecker_NBETerm.e_list e_ctor in
                              FStar_TypeChecker_NBETerm.unembed uu____4531 cb
                                dcs in
                            FStar_Util.bind_opt uu____4520
                              (fun dcs1 ->
                                 FStar_All.pipe_left
                                   (fun uu____4576 ->
                                      FStar_Pervasives_Native.Some uu____4576)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4584,
         (t1, uu____4586)::(ty, uu____4588)::(univs, uu____4590)::(fvar,
                                                                   uu____4592)::
         (r, uu____4594)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____4629 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r in
        FStar_Util.bind_opt uu____4629
          (fun r1 ->
             let uu____4635 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar in
             FStar_Util.bind_opt uu____4635
               (fun fvar1 ->
                  let uu____4641 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs in
                  FStar_Util.bind_opt uu____4641
                    (fun univs1 ->
                       let uu____4655 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty in
                       FStar_Util.bind_opt uu____4655
                         (fun ty1 ->
                            let uu____4661 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                            FStar_Util.bind_opt uu____4661
                              (fun t2 ->
                                 FStar_All.pipe_left
                                   (fun uu____4668 ->
                                      FStar_Pervasives_Native.Some uu____4668)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar1, univs1, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____4672, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4687 ->
        ((let uu____4689 =
            let uu____4694 =
              let uu____4695 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4695 in
            (FStar_Errors.Warning_NotEmbedded, uu____4694) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4689);
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
        let uu____4714 =
          let uu____4721 =
            let uu____4726 =
              FStar_TypeChecker_NBETerm.mk_t
                (FStar_TypeChecker_NBETerm.Constant
                   (FStar_TypeChecker_NBETerm.Int i)) in
            FStar_TypeChecker_NBETerm.as_arg uu____4726 in
          [uu____4721] in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4714
    | FStar_Reflection_Data.Mult (e1, e2) ->
        let uu____4737 =
          let uu____4744 =
            let uu____4749 = embed_exp cb e1 in
            FStar_TypeChecker_NBETerm.as_arg uu____4749 in
          let uu____4750 =
            let uu____4757 =
              let uu____4762 = embed_exp cb e2 in
              FStar_TypeChecker_NBETerm.as_arg uu____4762 in
            [uu____4757] in
          uu____4744 :: uu____4750 in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4737 in
  let rec unembed_exp cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____4791, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4807, (i, uu____4809)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____4828 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i in
        FStar_Util.bind_opt uu____4828
          (fun i1 ->
             FStar_All.pipe_left
               (fun uu____4835 -> FStar_Pervasives_Native.Some uu____4835)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4837, (e2, uu____4839)::(e1, uu____4841)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____4864 = unembed_exp cb e1 in
        FStar_Util.bind_opt uu____4864
          (fun e11 ->
             let uu____4870 = unembed_exp cb e2 in
             FStar_Util.bind_opt uu____4870
               (fun e21 ->
                  FStar_All.pipe_left
                    (fun uu____4877 ->
                       FStar_Pervasives_Native.Some uu____4877)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____4878 ->
        ((let uu____4880 =
            let uu____4885 =
              let uu____4886 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4886 in
            (FStar_Errors.Warning_NotEmbedded, uu____4885) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4880);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp_fv
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_bv e_aqualv
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding) = e_term
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_attribute
let (e_lid : FStar_Ident.lid FStar_TypeChecker_NBETerm.embedding) =
  let embed rng lid =
    let uu____4908 = FStar_Ident.path_of_lid lid in
    FStar_TypeChecker_NBETerm.embed e_string_list rng uu____4908 in
  let unembed cb t =
    let uu____4928 = FStar_TypeChecker_NBETerm.unembed e_string_list cb t in
    FStar_Util.map_opt uu____4928
      (fun p -> FStar_Ident.lid_of_path p FStar_Range.dummyRange) in
  let uu____4941 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] [] in
  let uu____4946 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed unembed uu____4941 uu____4946
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
        let uu____5029 =
          let uu____5036 =
            let uu____5041 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu____5041 in
          [uu____5036] in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.fv
          [] uu____5029
    | FStar_Reflection_Data.Discriminator l ->
        let uu____5051 =
          let uu____5058 =
            let uu____5063 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu____5063 in
          [uu____5058] in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.fv
          [] uu____5051
    | FStar_Reflection_Data.Action l ->
        let uu____5073 =
          let uu____5080 =
            let uu____5085 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu____5085 in
          [uu____5080] in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.fv []
          uu____5073
    | FStar_Reflection_Data.Projector (l, i) ->
        let uu____5096 =
          let uu____5103 =
            let uu____5108 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu____5108 in
          let uu____5109 =
            let uu____5116 =
              let uu____5121 = FStar_TypeChecker_NBETerm.embed e_ident cb i in
              FStar_TypeChecker_NBETerm.as_arg uu____5121 in
            [uu____5116] in
          uu____5103 :: uu____5109 in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.fv
          [] uu____5096
    | FStar_Reflection_Data.RecordType (ids1, ids2) ->
        let uu____5144 =
          let uu____5151 =
            let uu____5156 =
              let uu____5157 = FStar_TypeChecker_NBETerm.e_list e_ident in
              FStar_TypeChecker_NBETerm.embed uu____5157 cb ids1 in
            FStar_TypeChecker_NBETerm.as_arg uu____5156 in
          let uu____5164 =
            let uu____5171 =
              let uu____5176 =
                let uu____5177 = FStar_TypeChecker_NBETerm.e_list e_ident in
                FStar_TypeChecker_NBETerm.embed uu____5177 cb ids2 in
              FStar_TypeChecker_NBETerm.as_arg uu____5176 in
            [uu____5171] in
          uu____5151 :: uu____5164 in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.fv
          [] uu____5144
    | FStar_Reflection_Data.RecordConstructor (ids1, ids2) ->
        let uu____5206 =
          let uu____5213 =
            let uu____5218 =
              let uu____5219 = FStar_TypeChecker_NBETerm.e_list e_ident in
              FStar_TypeChecker_NBETerm.embed uu____5219 cb ids1 in
            FStar_TypeChecker_NBETerm.as_arg uu____5218 in
          let uu____5226 =
            let uu____5233 =
              let uu____5238 =
                let uu____5239 = FStar_TypeChecker_NBETerm.e_list e_ident in
                FStar_TypeChecker_NBETerm.embed uu____5239 cb ids2 in
              FStar_TypeChecker_NBETerm.as_arg uu____5238 in
            [uu____5233] in
          uu____5213 :: uu____5226 in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.fv
          [] uu____5206 in
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
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (l, uu____5496)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
        ->
        let uu____5513 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
        FStar_Util.bind_opt uu____5513
          (fun l1 ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Reflectable l1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (l, uu____5520)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
        ->
        let uu____5537 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
        FStar_Util.bind_opt uu____5537
          (fun l1 ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Discriminator l1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (l, uu____5544)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
        ->
        let uu____5561 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
        FStar_Util.bind_opt uu____5561
          (fun l1 ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Action l1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, [], (i, uu____5568)::(l, uu____5570)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
        ->
        let uu____5591 = FStar_TypeChecker_NBETerm.unembed e_ident cb i in
        FStar_Util.bind_opt uu____5591
          (fun i1 ->
             let uu____5597 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
             FStar_Util.bind_opt uu____5597
               (fun l1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Projector (l1, i1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, [], (ids2, uu____5604)::(ids1, uu____5606)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
        ->
        let uu____5627 =
          let uu____5632 = FStar_TypeChecker_NBETerm.e_list e_ident in
          FStar_TypeChecker_NBETerm.unembed uu____5632 cb ids1 in
        FStar_Util.bind_opt uu____5627
          (fun ids11 ->
             let uu____5646 =
               let uu____5651 = FStar_TypeChecker_NBETerm.e_list e_ident in
               FStar_TypeChecker_NBETerm.unembed uu____5651 cb ids2 in
             FStar_Util.bind_opt uu____5646
               (fun ids21 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordType (ids11, ids21))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, [], (ids2, uu____5670)::(ids1, uu____5672)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
        ->
        let uu____5693 =
          let uu____5698 = FStar_TypeChecker_NBETerm.e_list e_ident in
          FStar_TypeChecker_NBETerm.unembed uu____5698 cb ids1 in
        FStar_Util.bind_opt uu____5693
          (fun ids11 ->
             let uu____5712 =
               let uu____5717 = FStar_TypeChecker_NBETerm.e_list e_ident in
               FStar_TypeChecker_NBETerm.unembed uu____5717 cb ids2 in
             FStar_Util.bind_opt uu____5712
               (fun ids21 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordConstructor (ids11, ids21))))
    | uu____5734 ->
        ((let uu____5736 =
            let uu____5741 =
              let uu____5742 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded qualifier: %s" uu____5742 in
            (FStar_Errors.Warning_NotEmbedded, uu____5741) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5736);
         FStar_Pervasives_Native.None) in
  let uu____5743 =
    mkConstruct FStar_Reflection_Data.fstar_refl_qualifier_fv [] [] in
  let uu____5748 =
    fv_as_emb_typ FStar_Reflection_Data.fstar_refl_qualifier_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed unembed uu____5743 uu____5748
let (e_qualifiers :
  FStar_Reflection_Data.qualifier Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_qualifier