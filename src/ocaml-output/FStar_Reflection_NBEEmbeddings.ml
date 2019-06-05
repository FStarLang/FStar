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
    let uu____77 =
      let uu____85 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      (uu____85, []) in
    FStar_Syntax_Syntax.ET_app uu____77
let mk_emb' :
  'Auu____99 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____99 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____99 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____99 FStar_TypeChecker_NBETerm.embedding
  =
  fun x ->
    fun y ->
      fun fv ->
        let uu____141 = mkFV fv [] [] in
        let uu____146 = fv_as_emb_typ fv in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____141 uu____146
let mk_lazy :
  'Auu____158 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____158 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb ->
    fun obj ->
      fun ty ->
        fun kind ->
          let li =
            let uu____184 = FStar_Dyn.mkdyn obj in
            {
              FStar_Syntax_Syntax.blob = uu____184;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            } in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____190 ->
                 let uu____191 = FStar_Syntax_Util.unfold_lazy li in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____191) in
          FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk1)
let (e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv cb bv =
    mk_lazy cb bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv in
  let unembed_bv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv;
           FStar_Syntax_Syntax.ltyp = uu____236;
           FStar_Syntax_Syntax.rng = uu____237;_},
         uu____238)
        ->
        let uu____257 = FStar_Dyn.undyn b in
        FStar_All.pipe_left (fun _260 -> FStar_Pervasives_Native.Some _260)
          uu____257
    | uu____261 ->
        ((let uu____263 =
            let uu____269 =
              let uu____271 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded bv: %s" uu____271 in
            (FStar_Errors.Warning_NotEmbedded, uu____269) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____263);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv_fv
let (e_binder :
  FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding) =
  let embed_binder cb b =
    mk_lazy cb b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder in
  let unembed_binder cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder;
           FStar_Syntax_Syntax.ltyp = uu____305;
           FStar_Syntax_Syntax.rng = uu____306;_},
         uu____307)
        ->
        let uu____326 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____326
    | uu____327 ->
        ((let uu____329 =
            let uu____335 =
              let uu____337 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded binder: %s" uu____337 in
            (FStar_Errors.Warning_NotEmbedded, uu____335) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____329);
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
          let uu____387 = f x in
          FStar_Util.bind_opt uu____387
            (fun x1 ->
               let uu____395 = mapM_opt f xs in
               FStar_Util.bind_opt uu____395
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
      FStar_TypeChecker_NBETerm.Quote (t, qi) in
    let rec unembed_term cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Quote (tm, qi) ->
          FStar_Pervasives_Native.Some tm
      | uu____465 -> FStar_Pervasives_Native.None in
    let uu____466 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] [] in
    let uu____471 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____466;
      FStar_TypeChecker_NBETerm.emb_typ = uu____471
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
        let uu____504 =
          let uu____511 =
            let uu____516 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu____516 in
          [uu____511] in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____504 in
  let unembed_aqualv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (t1, uu____568)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____585 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu____585
          (fun t2 ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____590 ->
        ((let uu____592 =
            let uu____598 =
              let uu____600 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____600 in
            (FStar_Errors.Warning_NotEmbedded, uu____598) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____592);
         FStar_Pervasives_Native.None) in
  let uu____604 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] [] in
  let uu____609 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____604
    uu____609
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_list e_binder
let (e_fv : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding) =
  let embed_fv cb fv =
    mk_lazy cb fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar in
  let unembed_fv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar;
           FStar_Syntax_Syntax.ltyp = uu____643;
           FStar_Syntax_Syntax.rng = uu____644;_},
         uu____645)
        ->
        let uu____664 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____664
    | uu____665 ->
        ((let uu____667 =
            let uu____673 =
              let uu____675 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____675 in
            (FStar_Errors.Warning_NotEmbedded, uu____673) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____667);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv_fv
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp cb c =
    mk_lazy cb c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp in
  let unembed_comp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp;
           FStar_Syntax_Syntax.ltyp = uu____709;
           FStar_Syntax_Syntax.rng = uu____710;_},
         uu____711)
        ->
        let uu____730 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____730
    | uu____731 ->
        ((let uu____733 =
            let uu____739 =
              let uu____741 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded comp: %s" uu____741 in
            (FStar_Errors.Warning_NotEmbedded, uu____739) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____733);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp_fv
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env cb e =
    mk_lazy cb e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env in
  let unembed_env cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env;
           FStar_Syntax_Syntax.ltyp = uu____775;
           FStar_Syntax_Syntax.rng = uu____776;_},
         uu____777)
        ->
        let uu____796 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____796
    | uu____797 ->
        ((let uu____799 =
            let uu____805 =
              let uu____807 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded env: %s" uu____807 in
            (FStar_Errors.Warning_NotEmbedded, uu____805) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____799);
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
        let uu____838 =
          let uu____845 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i)) in
          [uu____845] in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____838
    | FStar_Reflection_Data.C_String s ->
        let uu____860 =
          let uu____867 =
            let uu____872 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s in
            FStar_TypeChecker_NBETerm.as_arg uu____872 in
          [uu____867] in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____860
    | FStar_Reflection_Data.C_Range r ->
        let uu____883 =
          let uu____890 =
            let uu____895 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r in
            FStar_TypeChecker_NBETerm.as_arg uu____895 in
          [uu____890] in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____883
    | FStar_Reflection_Data.C_Reify ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____909 =
          let uu____916 =
            let uu____921 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns in
            FStar_TypeChecker_NBETerm.as_arg uu____921 in
          [uu____916] in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____909 in
  let unembed_const cb t =
    match t with
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
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (i, uu____989)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____1006 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i in
        FStar_Util.bind_opt uu____1006
          (fun i1 ->
             FStar_All.pipe_left
               (fun _1013 -> FStar_Pervasives_Native.Some _1013)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (s, uu____1016)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____1033 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s in
        FStar_Util.bind_opt uu____1033
          (fun s1 ->
             FStar_All.pipe_left
               (fun _1044 -> FStar_Pervasives_Native.Some _1044)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (r, uu____1047)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____1064 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r in
        FStar_Util.bind_opt uu____1064
          (fun r1 ->
             FStar_All.pipe_left
               (fun _1071 -> FStar_Pervasives_Native.Some _1071)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (ns, uu____1087)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____1104 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns in
        FStar_Util.bind_opt uu____1104
          (fun ns1 ->
             FStar_All.pipe_left
               (fun _1123 -> FStar_Pervasives_Native.Some _1123)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____1124 ->
        ((let uu____1126 =
            let uu____1132 =
              let uu____1134 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____1134 in
            (FStar_Errors.Warning_NotEmbedded, uu____1132) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1126);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____1145 ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1158 =
            let uu____1165 =
              let uu____1170 = FStar_TypeChecker_NBETerm.embed e_const cb c in
              FStar_TypeChecker_NBETerm.as_arg uu____1170 in
            [uu____1165] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____1158
      | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
          let uu____1185 =
            let uu____1192 =
              let uu____1197 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu____1197 in
            let uu____1198 =
              let uu____1205 =
                let uu____1210 =
                  let uu____1211 =
                    let uu____1216 = e_pattern' () in
                    FStar_TypeChecker_NBETerm.e_list uu____1216 in
                  FStar_TypeChecker_NBETerm.embed uu____1211 cb ps in
                FStar_TypeChecker_NBETerm.as_arg uu____1210 in
              [uu____1205] in
            uu____1192 :: uu____1198 in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1185
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1234 =
            let uu____1241 =
              let uu____1246 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1246 in
            [uu____1241] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1234
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1256 =
            let uu____1263 =
              let uu____1268 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1268 in
            [uu____1263] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1256
      | FStar_Reflection_Data.Pat_Dot_Term (bv, t) ->
          let uu____1279 =
            let uu____1286 =
              let uu____1291 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1291 in
            let uu____1292 =
              let uu____1299 =
                let uu____1304 = FStar_TypeChecker_NBETerm.embed e_term cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____1304 in
              [uu____1299] in
            uu____1286 :: uu____1292 in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1279 in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (c, uu____1334)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1351 = FStar_TypeChecker_NBETerm.unembed e_const cb c in
          FStar_Util.bind_opt uu____1351
            (fun c1 ->
               FStar_All.pipe_left
                 (fun _1358 -> FStar_Pervasives_Native.Some _1358)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, [], (ps, uu____1361)::(f, uu____1363)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1384 = FStar_TypeChecker_NBETerm.unembed e_fv cb f in
          FStar_Util.bind_opt uu____1384
            (fun f1 ->
               let uu____1390 =
                 let uu____1395 =
                   let uu____1400 = e_pattern' () in
                   FStar_TypeChecker_NBETerm.e_list uu____1400 in
                 FStar_TypeChecker_NBETerm.unembed uu____1395 cb ps in
               FStar_Util.bind_opt uu____1390
                 (fun ps1 ->
                    FStar_All.pipe_left
                      (fun _1413 -> FStar_Pervasives_Native.Some _1413)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (bv, uu____1418)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1435 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu____1435
            (fun bv1 ->
               FStar_All.pipe_left
                 (fun _1442 -> FStar_Pervasives_Native.Some _1442)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (bv, uu____1445)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1462 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu____1462
            (fun bv1 ->
               FStar_All.pipe_left
                 (fun _1469 -> FStar_Pervasives_Native.Some _1469)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, [], (t1, uu____1472)::(bv, uu____1474)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1495 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu____1495
            (fun bv1 ->
               let uu____1501 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____1501
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun _1508 -> FStar_Pervasives_Native.Some _1508)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1509 ->
          ((let uu____1511 =
              let uu____1517 =
                let uu____1519 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1519 in
              (FStar_Errors.Warning_NotEmbedded, uu____1517) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1511);
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
    let uu____1560 = e_term_aq aq in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1560
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let uu____1591 = e_term_aq aq in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1591 e_aqualv
let rec unlazy_as_t :
  'Auu____1601 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1601
  =
  fun k ->
    fun t ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____1614;
             FStar_Syntax_Syntax.rng = uu____1615;_},
           uu____1616)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1635 -> failwith "Not a Lazy of the expected kind (NBE)"
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1673 =
            let uu____1680 =
              let uu____1685 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu____1685 in
            [uu____1680] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1673
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1695 =
            let uu____1702 =
              let uu____1707 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1707 in
            [uu____1702] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1695
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1717 =
            let uu____1724 =
              let uu____1729 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1729 in
            [uu____1724] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1717
      | FStar_Reflection_Data.Tv_App (hd1, a) ->
          let uu____1740 =
            let uu____1747 =
              let uu____1752 =
                let uu____1753 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____1753 cb hd1 in
              FStar_TypeChecker_NBETerm.as_arg uu____1752 in
            let uu____1756 =
              let uu____1763 =
                let uu____1768 =
                  let uu____1769 = e_argv_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____1769 cb a in
                FStar_TypeChecker_NBETerm.as_arg uu____1768 in
              [uu____1763] in
            uu____1747 :: uu____1756 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1740
      | FStar_Reflection_Data.Tv_Abs (b, t) ->
          let uu____1794 =
            let uu____1801 =
              let uu____1806 = FStar_TypeChecker_NBETerm.embed e_binder cb b in
              FStar_TypeChecker_NBETerm.as_arg uu____1806 in
            let uu____1807 =
              let uu____1814 =
                let uu____1819 =
                  let uu____1820 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____1820 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____1819 in
              [uu____1814] in
            uu____1801 :: uu____1807 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1794
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          let uu____1837 =
            let uu____1844 =
              let uu____1849 = FStar_TypeChecker_NBETerm.embed e_binder cb b in
              FStar_TypeChecker_NBETerm.as_arg uu____1849 in
            let uu____1850 =
              let uu____1857 =
                let uu____1862 = FStar_TypeChecker_NBETerm.embed e_comp cb c in
                FStar_TypeChecker_NBETerm.as_arg uu____1862 in
              [uu____1857] in
            uu____1844 :: uu____1850 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1837
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1876 =
            let uu____1883 =
              let uu____1888 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb () in
              FStar_TypeChecker_NBETerm.as_arg uu____1888 in
            [uu____1883] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1876
      | FStar_Reflection_Data.Tv_Refine (bv, t) ->
          let uu____1899 =
            let uu____1906 =
              let uu____1911 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1911 in
            let uu____1912 =
              let uu____1919 =
                let uu____1924 =
                  let uu____1925 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____1925 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____1924 in
              [uu____1919] in
            uu____1906 :: uu____1912 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1899
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1941 =
            let uu____1948 =
              let uu____1953 = FStar_TypeChecker_NBETerm.embed e_const cb c in
              FStar_TypeChecker_NBETerm.as_arg uu____1953 in
            [uu____1948] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1941
      | FStar_Reflection_Data.Tv_Uvar (u, d) ->
          let uu____1964 =
            let uu____1971 =
              let uu____1976 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u in
              FStar_TypeChecker_NBETerm.as_arg uu____1976 in
            let uu____1977 =
              let uu____1984 =
                let uu____1989 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar in
                FStar_TypeChecker_NBETerm.as_arg uu____1989 in
              [uu____1984] in
            uu____1971 :: uu____1977 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____1964
      | FStar_Reflection_Data.Tv_Let (r, b, t1, t2) ->
          let uu____2012 =
            let uu____2019 =
              let uu____2024 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r in
              FStar_TypeChecker_NBETerm.as_arg uu____2024 in
            let uu____2026 =
              let uu____2033 =
                let uu____2038 = FStar_TypeChecker_NBETerm.embed e_bv cb b in
                FStar_TypeChecker_NBETerm.as_arg uu____2038 in
              let uu____2039 =
                let uu____2046 =
                  let uu____2051 =
                    let uu____2052 = e_term_aq aq in
                    FStar_TypeChecker_NBETerm.embed uu____2052 cb t1 in
                  FStar_TypeChecker_NBETerm.as_arg uu____2051 in
                let uu____2055 =
                  let uu____2062 =
                    let uu____2067 =
                      let uu____2068 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.embed uu____2068 cb t2 in
                    FStar_TypeChecker_NBETerm.as_arg uu____2067 in
                  [uu____2062] in
                uu____2046 :: uu____2055 in
              uu____2033 :: uu____2039 in
            uu____2019 :: uu____2026 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____2012
      | FStar_Reflection_Data.Tv_Match (t, brs) ->
          let uu____2097 =
            let uu____2104 =
              let uu____2109 =
                let uu____2110 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____2110 cb t in
              FStar_TypeChecker_NBETerm.as_arg uu____2109 in
            let uu____2113 =
              let uu____2120 =
                let uu____2125 =
                  let uu____2126 =
                    let uu____2135 = e_branch_aq aq in
                    FStar_TypeChecker_NBETerm.e_list uu____2135 in
                  FStar_TypeChecker_NBETerm.embed uu____2126 cb brs in
                FStar_TypeChecker_NBETerm.as_arg uu____2125 in
              [uu____2120] in
            uu____2104 :: uu____2113 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2097
      | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
          let uu____2171 =
            let uu____2178 =
              let uu____2183 =
                let uu____2184 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____2184 cb e in
              FStar_TypeChecker_NBETerm.as_arg uu____2183 in
            let uu____2187 =
              let uu____2194 =
                let uu____2199 =
                  let uu____2200 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____2200 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____2199 in
              let uu____2203 =
                let uu____2210 =
                  let uu____2215 =
                    let uu____2216 =
                      let uu____2221 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.e_option uu____2221 in
                    FStar_TypeChecker_NBETerm.embed uu____2216 cb tacopt in
                  FStar_TypeChecker_NBETerm.as_arg uu____2215 in
                [uu____2210] in
              uu____2194 :: uu____2203 in
            uu____2178 :: uu____2187 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2171
      | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
          let uu____2249 =
            let uu____2256 =
              let uu____2261 =
                let uu____2262 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____2262 cb e in
              FStar_TypeChecker_NBETerm.as_arg uu____2261 in
            let uu____2265 =
              let uu____2272 =
                let uu____2277 = FStar_TypeChecker_NBETerm.embed e_comp cb c in
                FStar_TypeChecker_NBETerm.as_arg uu____2277 in
              let uu____2278 =
                let uu____2285 =
                  let uu____2290 =
                    let uu____2291 =
                      let uu____2296 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.e_option uu____2296 in
                    FStar_TypeChecker_NBETerm.embed uu____2291 cb tacopt in
                  FStar_TypeChecker_NBETerm.as_arg uu____2290 in
                [uu____2285] in
              uu____2272 :: uu____2278 in
            uu____2256 :: uu____2265 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2249
      | FStar_Reflection_Data.Tv_Unknown ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            [] in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2337, (b, uu____2339)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2358 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu____2358
            (fun b1 ->
               FStar_All.pipe_left
                 (fun _2365 -> FStar_Pervasives_Native.Some _2365)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2367, (b, uu____2369)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2388 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu____2388
            (fun b1 ->
               FStar_All.pipe_left
                 (fun _2395 -> FStar_Pervasives_Native.Some _2395)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2397, (f, uu____2399)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2418 = FStar_TypeChecker_NBETerm.unembed e_fv cb f in
          FStar_Util.bind_opt uu____2418
            (fun f1 ->
               FStar_All.pipe_left
                 (fun _2425 -> FStar_Pervasives_Native.Some _2425)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2427, (r, uu____2429)::(l, uu____2431)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2454 = FStar_TypeChecker_NBETerm.unembed e_term cb l in
          FStar_Util.bind_opt uu____2454
            (fun l1 ->
               let uu____2460 = FStar_TypeChecker_NBETerm.unembed e_argv cb r in
               FStar_Util.bind_opt uu____2460
                 (fun r1 ->
                    FStar_All.pipe_left
                      (fun _2467 -> FStar_Pervasives_Native.Some _2467)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2469, (t1, uu____2471)::(b, uu____2473)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2496 = FStar_TypeChecker_NBETerm.unembed e_binder cb b in
          FStar_Util.bind_opt uu____2496
            (fun b1 ->
               let uu____2502 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____2502
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun _2509 -> FStar_Pervasives_Native.Some _2509)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2511, (t1, uu____2513)::(b, uu____2515)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2538 = FStar_TypeChecker_NBETerm.unembed e_binder cb b in
          FStar_Util.bind_opt uu____2538
            (fun b1 ->
               let uu____2544 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1 in
               FStar_Util.bind_opt uu____2544
                 (fun c ->
                    FStar_All.pipe_left
                      (fun _2551 -> FStar_Pervasives_Native.Some _2551)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2553, (u, uu____2555)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2574 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u in
          FStar_Util.bind_opt uu____2574
            (fun u1 ->
               FStar_All.pipe_left
                 (fun _2581 -> FStar_Pervasives_Native.Some _2581)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2583, (t1, uu____2585)::(b, uu____2587)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2610 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu____2610
            (fun b1 ->
               let uu____2616 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____2616
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun _2623 -> FStar_Pervasives_Native.Some _2623)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2625, (c, uu____2627)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2646 = FStar_TypeChecker_NBETerm.unembed e_const cb c in
          FStar_Util.bind_opt uu____2646
            (fun c1 ->
               FStar_All.pipe_left
                 (fun _2653 -> FStar_Pervasives_Native.Some _2653)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2655, (l, uu____2657)::(u, uu____2659)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2682 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u in
          FStar_Util.bind_opt uu____2682
            (fun u1 ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l in
               FStar_All.pipe_left
                 (fun _2691 -> FStar_Pervasives_Native.Some _2691)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2693,
           (t2, uu____2695)::(t1, uu____2697)::(b, uu____2699)::(r,
                                                                 uu____2701)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2732 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r in
          FStar_Util.bind_opt uu____2732
            (fun r1 ->
               let uu____2742 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
               FStar_Util.bind_opt uu____2742
                 (fun b1 ->
                    let uu____2748 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                    FStar_Util.bind_opt uu____2748
                      (fun t11 ->
                         let uu____2754 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2 in
                         FStar_Util.bind_opt uu____2754
                           (fun t21 ->
                              FStar_All.pipe_left
                                (fun _2761 ->
                                   FStar_Pervasives_Native.Some _2761)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2764, (brs, uu____2766)::(t1, uu____2768)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2791 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
          FStar_Util.bind_opt uu____2791
            (fun t2 ->
               let uu____2797 =
                 let uu____2802 = FStar_TypeChecker_NBETerm.e_list e_branch in
                 FStar_TypeChecker_NBETerm.unembed uu____2802 cb brs in
               FStar_Util.bind_opt uu____2797
                 (fun brs1 ->
                    FStar_All.pipe_left
                      (fun _2817 -> FStar_Pervasives_Native.Some _2817)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2821,
           (tacopt, uu____2823)::(t1, uu____2825)::(e, uu____2827)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2854 = FStar_TypeChecker_NBETerm.unembed e_term cb e in
          FStar_Util.bind_opt uu____2854
            (fun e1 ->
               let uu____2860 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____2860
                 (fun t2 ->
                    let uu____2866 =
                      let uu____2871 =
                        FStar_TypeChecker_NBETerm.e_option e_term in
                      FStar_TypeChecker_NBETerm.unembed uu____2871 cb tacopt in
                    FStar_Util.bind_opt uu____2866
                      (fun tacopt1 ->
                         FStar_All.pipe_left
                           (fun _2886 -> FStar_Pervasives_Native.Some _2886)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2890,
           (tacopt, uu____2892)::(c, uu____2894)::(e, uu____2896)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____2923 = FStar_TypeChecker_NBETerm.unembed e_term cb e in
          FStar_Util.bind_opt uu____2923
            (fun e1 ->
               let uu____2929 = FStar_TypeChecker_NBETerm.unembed e_comp cb c in
               FStar_Util.bind_opt uu____2929
                 (fun c1 ->
                    let uu____2935 =
                      let uu____2940 =
                        FStar_TypeChecker_NBETerm.e_option e_term in
                      FStar_TypeChecker_NBETerm.unembed uu____2940 cb tacopt in
                    FStar_Util.bind_opt uu____2935
                      (fun tacopt1 ->
                         FStar_All.pipe_left
                           (fun _2955 -> FStar_Pervasives_Native.Some _2955)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv, uu____2959, []) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _2976 -> FStar_Pervasives_Native.Some _2976)
            FStar_Reflection_Data.Tv_Unknown
      | uu____2977 ->
          ((let uu____2979 =
              let uu____2985 =
                let uu____2987 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____2987 in
              (FStar_Errors.Warning_NotEmbedded, uu____2985) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2979);
           FStar_Pervasives_Native.None) in
    mk_emb' embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view_fv
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq []
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view cb bvv =
    let uu____3014 =
      let uu____3021 =
        let uu____3026 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname in
        FStar_TypeChecker_NBETerm.as_arg uu____3026 in
      let uu____3028 =
        let uu____3035 =
          let uu____3040 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index in
          FStar_TypeChecker_NBETerm.as_arg uu____3040 in
        let uu____3041 =
          let uu____3048 =
            let uu____3053 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort in
            FStar_TypeChecker_NBETerm.as_arg uu____3053 in
          [uu____3048] in
        uu____3035 :: uu____3041 in
      uu____3021 :: uu____3028 in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____3014 in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3086,
         (s, uu____3088)::(idx, uu____3090)::(nm, uu____3092)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____3119 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm in
        FStar_Util.bind_opt uu____3119
          (fun nm1 ->
             let uu____3129 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx in
             FStar_Util.bind_opt uu____3129
               (fun idx1 ->
                  let uu____3135 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s in
                  FStar_Util.bind_opt uu____3135
                    (fun s1 ->
                       FStar_All.pipe_left
                         (fun _3142 -> FStar_Pervasives_Native.Some _3142)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____3143 ->
        ((let uu____3145 =
            let uu____3151 =
              let uu____3153 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3153 in
            (FStar_Errors.Warning_NotEmbedded, uu____3151) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3145);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t, md) ->
        let uu____3177 =
          let uu____3184 =
            let uu____3189 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu____3189 in
          let uu____3190 =
            let uu____3197 =
              let uu____3202 =
                let uu____3203 = FStar_TypeChecker_NBETerm.e_option e_term in
                FStar_TypeChecker_NBETerm.embed uu____3203 cb md in
              FStar_TypeChecker_NBETerm.as_arg uu____3202 in
            [uu____3197] in
          uu____3184 :: uu____3190 in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3177
    | FStar_Reflection_Data.C_Lemma (pre, post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
        let uu____3227 =
          let uu____3234 =
            let uu____3239 = FStar_TypeChecker_NBETerm.embed e_term cb pre in
            FStar_TypeChecker_NBETerm.as_arg uu____3239 in
          let uu____3240 =
            let uu____3247 =
              let uu____3252 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1 in
              FStar_TypeChecker_NBETerm.as_arg uu____3252 in
            [uu____3247] in
          uu____3234 :: uu____3240 in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3227
    | FStar_Reflection_Data.C_Unknown ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] [] in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3285, (md, uu____3287)::(t1, uu____3289)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3312 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu____3312
          (fun t2 ->
             let uu____3318 =
               let uu____3323 = FStar_TypeChecker_NBETerm.e_option e_term in
               FStar_TypeChecker_NBETerm.unembed uu____3323 cb md in
             FStar_Util.bind_opt uu____3318
               (fun md1 ->
                  FStar_All.pipe_left
                    (fun _3338 -> FStar_Pervasives_Native.Some _3338)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3342, (post, uu____3344)::(pre, uu____3346)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3369 = FStar_TypeChecker_NBETerm.unembed e_term cb pre in
        FStar_Util.bind_opt uu____3369
          (fun pre1 ->
             let uu____3375 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post in
             FStar_Util.bind_opt uu____3375
               (fun post1 ->
                  FStar_All.pipe_left
                    (fun _3382 -> FStar_Pervasives_Native.Some _3382)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3384, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left (fun _3401 -> FStar_Pervasives_Native.Some _3401)
          FStar_Reflection_Data.C_Unknown
    | uu____3402 ->
        ((let uu____3404 =
            let uu____3410 =
              let uu____3412 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3412 in
            (FStar_Errors.Warning_NotEmbedded, uu____3410) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3404);
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
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3458, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3474, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3490, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____3505 ->
        ((let uu____3507 =
            let uu____3513 =
              let uu____3515 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded order: %s" uu____3515 in
            (FStar_Errors.Warning_NotEmbedded, uu____3513) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3507);
         FStar_Pervasives_Native.None) in
  let uu____3519 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  mk_emb' embed_order unembed_order uu____3519
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt cb se =
    mk_lazy cb se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt in
  let unembed_sigelt cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt;
           FStar_Syntax_Syntax.ltyp = uu____3550;
           FStar_Syntax_Syntax.rng = uu____3551;_},
         uu____3552)
        ->
        let uu____3571 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____3571
    | uu____3572 ->
        ((let uu____3574 =
            let uu____3580 =
              let uu____3582 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3582 in
            (FStar_Errors.Warning_NotEmbedded, uu____3580) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3574);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt_fv
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string in
  let embed_ident cb i =
    let uu____3611 =
      let uu____3617 = FStar_Ident.range_of_id i in
      let uu____3618 = FStar_Ident.text_of_id i in (uu____3617, uu____3618) in
    FStar_TypeChecker_NBETerm.embed repr cb uu____3611 in
  let unembed_ident cb t =
    let uu____3641 = FStar_TypeChecker_NBETerm.unembed repr cb t in
    match uu____3641 with
    | FStar_Pervasives_Native.Some (rng, s) ->
        let uu____3665 = FStar_Ident.mk_ident (s, rng) in
        FStar_Pervasives_Native.Some uu____3665
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let range_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  let string_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  let et =
    let uu____3675 =
      let uu____3683 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2 in
      let uu____3685 =
        let uu____3688 = fv_as_emb_typ range_fv in
        let uu____3689 =
          let uu____3692 = fv_as_emb_typ string_fv in [uu____3692] in
        uu____3688 :: uu____3689 in
      (uu____3683, uu____3685) in
    FStar_Syntax_Syntax.ET_app uu____3675 in
  let uu____3696 =
    let uu____3697 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    let uu____3698 =
      let uu____3705 =
        let uu____3710 = mkFV range_fv [] [] in
        FStar_TypeChecker_NBETerm.as_arg uu____3710 in
      let uu____3715 =
        let uu____3722 =
          let uu____3727 = mkFV string_fv [] [] in
          FStar_TypeChecker_NBETerm.as_arg uu____3727 in
        [uu____3722] in
      uu____3705 :: uu____3715 in
    mkFV uu____3697 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____3698 in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3696 et
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
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt_view cb sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r, fv, univs1, ty, t) ->
        let uu____3784 =
          let uu____3791 =
            let uu____3796 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r in
            FStar_TypeChecker_NBETerm.as_arg uu____3796 in
          let uu____3798 =
            let uu____3805 =
              let uu____3810 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu____3810 in
            let uu____3811 =
              let uu____3818 =
                let uu____3823 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1 in
                FStar_TypeChecker_NBETerm.as_arg uu____3823 in
              let uu____3826 =
                let uu____3833 =
                  let uu____3838 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty in
                  FStar_TypeChecker_NBETerm.as_arg uu____3838 in
                let uu____3839 =
                  let uu____3846 =
                    let uu____3851 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t in
                    FStar_TypeChecker_NBETerm.as_arg uu____3851 in
                  [uu____3846] in
                uu____3833 :: uu____3839 in
              uu____3818 :: uu____3826 in
            uu____3805 :: uu____3811 in
          uu____3791 :: uu____3798 in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____3784
    | FStar_Reflection_Data.Sg_Constructor (nm, ty) ->
        let uu____3878 =
          let uu____3885 =
            let uu____3890 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm in
            FStar_TypeChecker_NBETerm.as_arg uu____3890 in
          let uu____3894 =
            let uu____3901 =
              let uu____3906 = FStar_TypeChecker_NBETerm.embed e_term cb ty in
              FStar_TypeChecker_NBETerm.as_arg uu____3906 in
            [uu____3901] in
          uu____3885 :: uu____3894 in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____3878
    | FStar_Reflection_Data.Sg_Inductive (nm, univs1, bs, t, dcs) ->
        let uu____3936 =
          let uu____3943 =
            let uu____3948 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm in
            FStar_TypeChecker_NBETerm.as_arg uu____3948 in
          let uu____3952 =
            let uu____3959 =
              let uu____3964 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1 in
              FStar_TypeChecker_NBETerm.as_arg uu____3964 in
            let uu____3967 =
              let uu____3974 =
                let uu____3979 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs in
                FStar_TypeChecker_NBETerm.as_arg uu____3979 in
              let uu____3980 =
                let uu____3987 =
                  let uu____3992 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t in
                  FStar_TypeChecker_NBETerm.as_arg uu____3992 in
                let uu____3993 =
                  let uu____4000 =
                    let uu____4005 =
                      let uu____4006 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list in
                      FStar_TypeChecker_NBETerm.embed uu____4006 cb dcs in
                    FStar_TypeChecker_NBETerm.as_arg uu____4005 in
                  [uu____4000] in
                uu____3987 :: uu____3993 in
              uu____3974 :: uu____3980 in
            uu____3959 :: uu____3967 in
          uu____3943 :: uu____3952 in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____3936
    | FStar_Reflection_Data.Unk ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          [] in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4066,
         (dcs, uu____4068)::(t1, uu____4070)::(bs, uu____4072)::(us,
                                                                 uu____4074)::
         (nm, uu____4076)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____4111 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm in
        FStar_Util.bind_opt uu____4111
          (fun nm1 ->
             let uu____4129 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us in
             FStar_Util.bind_opt uu____4129
               (fun us1 ->
                  let uu____4143 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs in
                  FStar_Util.bind_opt uu____4143
                    (fun bs1 ->
                       let uu____4149 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                       FStar_Util.bind_opt uu____4149
                         (fun t2 ->
                            let uu____4155 =
                              let uu____4163 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list in
                              FStar_TypeChecker_NBETerm.unembed uu____4163 cb
                                dcs in
                            FStar_Util.bind_opt uu____4155
                              (fun dcs1 ->
                                 FStar_All.pipe_left
                                   (fun _4193 ->
                                      FStar_Pervasives_Native.Some _4193)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4201,
         (t1, uu____4203)::(ty, uu____4205)::(univs1, uu____4207)::(fvar1,
                                                                    uu____4209)::
         (r, uu____4211)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____4246 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r in
        FStar_Util.bind_opt uu____4246
          (fun r1 ->
             let uu____4256 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1 in
             FStar_Util.bind_opt uu____4256
               (fun fvar2 ->
                  let uu____4262 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1 in
                  FStar_Util.bind_opt uu____4262
                    (fun univs2 ->
                       let uu____4276 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty in
                       FStar_Util.bind_opt uu____4276
                         (fun ty1 ->
                            let uu____4282 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                            FStar_Util.bind_opt uu____4282
                              (fun t2 ->
                                 FStar_All.pipe_left
                                   (fun _4289 ->
                                      FStar_Pervasives_Native.Some _4289)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____4294, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4309 ->
        ((let uu____4311 =
            let uu____4317 =
              let uu____4319 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4319 in
            (FStar_Errors.Warning_NotEmbedded, uu____4317) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4311);
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
        let uu____4342 =
          let uu____4349 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i)) in
          [uu____4349] in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4342
    | FStar_Reflection_Data.Mult (e1, e2) ->
        let uu____4364 =
          let uu____4371 =
            let uu____4376 = embed_exp cb e1 in
            FStar_TypeChecker_NBETerm.as_arg uu____4376 in
          let uu____4377 =
            let uu____4384 =
              let uu____4389 = embed_exp cb e2 in
              FStar_TypeChecker_NBETerm.as_arg uu____4389 in
            [uu____4384] in
          uu____4371 :: uu____4377 in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4364 in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____4418, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4434, (i, uu____4436)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____4455 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i in
        FStar_Util.bind_opt uu____4455
          (fun i1 ->
             FStar_All.pipe_left
               (fun _4462 -> FStar_Pervasives_Native.Some _4462)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4464, (e2, uu____4466)::(e1, uu____4468)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____4491 = unembed_exp cb e1 in
        FStar_Util.bind_opt uu____4491
          (fun e11 ->
             let uu____4497 = unembed_exp cb e2 in
             FStar_Util.bind_opt uu____4497
               (fun e21 ->
                  FStar_All.pipe_left
                    (fun _4504 -> FStar_Pervasives_Native.Some _4504)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____4505 ->
        ((let uu____4507 =
            let uu____4513 =
              let uu____4515 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4515 in
            (FStar_Errors.Warning_NotEmbedded, uu____4513) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4507);
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