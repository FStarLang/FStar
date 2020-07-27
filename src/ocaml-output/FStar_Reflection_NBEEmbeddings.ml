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
          [] uu____541 in
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
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (t1, uu____605)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____622 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu____622
          (fun t2 ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____627 ->
        ((let uu____629 =
            let uu____634 =
              let uu____635 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____635 in
            (FStar_Errors.Warning_NotEmbedded, uu____634) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____629);
         FStar_Pervasives_Native.None) in
  let uu____636 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] [] in
  let uu____641 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____636
    uu____641
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
           FStar_Syntax_Syntax.ltyp = uu____673;
           FStar_Syntax_Syntax.rng = uu____674;_},
         uu____675)
        ->
        let uu____694 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____694
    | uu____695 ->
        ((let uu____697 =
            let uu____702 =
              let uu____703 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____703 in
            (FStar_Errors.Warning_NotEmbedded, uu____702) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____697);
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
           FStar_Syntax_Syntax.ltyp = uu____733;
           FStar_Syntax_Syntax.rng = uu____734;_},
         uu____735)
        ->
        let uu____754 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____754
    | uu____755 ->
        ((let uu____757 =
            let uu____762 =
              let uu____763 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded comp: %s" uu____763 in
            (FStar_Errors.Warning_NotEmbedded, uu____762) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____757);
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
           FStar_Syntax_Syntax.ltyp = uu____793;
           FStar_Syntax_Syntax.rng = uu____794;_},
         uu____795)
        ->
        let uu____814 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____814
    | uu____815 ->
        ((let uu____817 =
            let uu____822 =
              let uu____823 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded env: %s" uu____823 in
            (FStar_Errors.Warning_NotEmbedded, uu____822) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____817);
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
        let uu____850 =
          let uu____857 =
            let uu____862 =
              FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
                (FStar_TypeChecker_NBETerm.Constant
                   (FStar_TypeChecker_NBETerm.Int i)) in
            FStar_TypeChecker_NBETerm.as_arg uu____862 in
          [uu____857] in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____850
    | FStar_Reflection_Data.C_String s ->
        let uu____872 =
          let uu____879 =
            let uu____884 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s in
            FStar_TypeChecker_NBETerm.as_arg uu____884 in
          [uu____879] in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____872
    | FStar_Reflection_Data.C_Range r ->
        let uu____894 =
          let uu____901 =
            let uu____906 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r in
            FStar_TypeChecker_NBETerm.as_arg uu____906 in
          [uu____901] in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____894
    | FStar_Reflection_Data.C_Reify ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____920 =
          let uu____927 =
            let uu____932 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns in
            FStar_TypeChecker_NBETerm.as_arg uu____932 in
          [uu____927] in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____920 in
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
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (i, uu____999)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____1016 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i in
        FStar_Util.bind_opt uu____1016
          (fun i1 ->
             FStar_All.pipe_left
               (fun uu____1023 -> FStar_Pervasives_Native.Some uu____1023)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (s, uu____1026)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____1043 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s in
        FStar_Util.bind_opt uu____1043
          (fun s1 ->
             FStar_All.pipe_left
               (fun uu____1050 -> FStar_Pervasives_Native.Some uu____1050)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (r, uu____1053)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____1070 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r in
        FStar_Util.bind_opt uu____1070
          (fun r1 ->
             FStar_All.pipe_left
               (fun uu____1077 -> FStar_Pervasives_Native.Some uu____1077)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (ns, uu____1093)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____1110 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns in
        FStar_Util.bind_opt uu____1110
          (fun ns1 ->
             FStar_All.pipe_left
               (fun uu____1125 -> FStar_Pervasives_Native.Some uu____1125)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____1126 ->
        ((let uu____1128 =
            let uu____1133 =
              let uu____1134 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____1134 in
            (FStar_Errors.Warning_NotEmbedded, uu____1133) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1128);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____1141 ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1154 =
            let uu____1161 =
              let uu____1166 = FStar_TypeChecker_NBETerm.embed e_const cb c in
              FStar_TypeChecker_NBETerm.as_arg uu____1166 in
            [uu____1161] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____1154
      | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
          let uu____1189 =
            let uu____1196 =
              let uu____1201 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu____1201 in
            let uu____1202 =
              let uu____1209 =
                let uu____1214 =
                  let uu____1215 =
                    let uu____1224 =
                      let uu____1231 = e_pattern' () in
                      FStar_TypeChecker_NBETerm.e_tuple2 uu____1231
                        FStar_TypeChecker_NBETerm.e_bool in
                    FStar_TypeChecker_NBETerm.e_list uu____1224 in
                  FStar_TypeChecker_NBETerm.embed uu____1215 cb ps in
                FStar_TypeChecker_NBETerm.as_arg uu____1214 in
              [uu____1209] in
            uu____1196 :: uu____1202 in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1189
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1257 =
            let uu____1264 =
              let uu____1269 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1269 in
            [uu____1264] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1257
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1279 =
            let uu____1286 =
              let uu____1291 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1291 in
            [uu____1286] in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1279
      | FStar_Reflection_Data.Pat_Dot_Term (bv, t) ->
          let uu____1302 =
            let uu____1309 =
              let uu____1314 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1314 in
            let uu____1315 =
              let uu____1322 =
                let uu____1327 = FStar_TypeChecker_NBETerm.embed e_term cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____1327 in
              [uu____1322] in
            uu____1309 :: uu____1315 in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1302 in
    let unembed_pattern cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (c, uu____1357)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1374 = FStar_TypeChecker_NBETerm.unembed e_const cb c in
          FStar_Util.bind_opt uu____1374
            (fun c1 ->
               FStar_All.pipe_left
                 (fun uu____1381 -> FStar_Pervasives_Native.Some uu____1381)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, [], (ps, uu____1384)::(f, uu____1386)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1407 = FStar_TypeChecker_NBETerm.unembed e_fv cb f in
          FStar_Util.bind_opt uu____1407
            (fun f1 ->
               let uu____1413 =
                 let uu____1422 =
                   let uu____1431 =
                     let uu____1438 = e_pattern' () in
                     FStar_TypeChecker_NBETerm.e_tuple2 uu____1438
                       FStar_TypeChecker_NBETerm.e_bool in
                   FStar_TypeChecker_NBETerm.e_list uu____1431 in
                 FStar_TypeChecker_NBETerm.unembed uu____1422 cb ps in
               FStar_Util.bind_opt uu____1413
                 (fun ps1 ->
                    FStar_All.pipe_left
                      (fun uu____1467 ->
                         FStar_Pervasives_Native.Some uu____1467)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (bv, uu____1476)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1493 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu____1493
            (fun bv1 ->
               FStar_All.pipe_left
                 (fun uu____1500 -> FStar_Pervasives_Native.Some uu____1500)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv, [], (bv, uu____1503)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1520 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu____1520
            (fun bv1 ->
               FStar_All.pipe_left
                 (fun uu____1527 -> FStar_Pervasives_Native.Some uu____1527)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, [], (t1, uu____1530)::(bv, uu____1532)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1553 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv in
          FStar_Util.bind_opt uu____1553
            (fun bv1 ->
               let uu____1559 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____1559
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun uu____1566 ->
                         FStar_Pervasives_Native.Some uu____1566)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1567 ->
          ((let uu____1569 =
              let uu____1574 =
                let uu____1575 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1575 in
              (FStar_Errors.Warning_NotEmbedded, uu____1574) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1569);
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
    let uu____1609 = e_term_aq aq in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1609
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let uu____1639 = e_term_aq aq in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1639 e_aqualv
let unlazy_as_t :
  'uuuuuu1648 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'uuuuuu1648
  =
  fun k ->
    fun t ->
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____1661;
             FStar_Syntax_Syntax.rng = uu____1662;_},
           uu____1663)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____1682 -> failwith "Not a Lazy of the expected kind (NBE)"
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1718 =
            let uu____1725 =
              let uu____1730 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu____1730 in
            [uu____1725] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1718
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1740 =
            let uu____1747 =
              let uu____1752 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1752 in
            [uu____1747] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1740
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1762 =
            let uu____1769 =
              let uu____1774 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1774 in
            [uu____1769] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1762
      | FStar_Reflection_Data.Tv_App (hd, a) ->
          let uu____1785 =
            let uu____1792 =
              let uu____1797 =
                let uu____1798 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____1798 cb hd in
              FStar_TypeChecker_NBETerm.as_arg uu____1797 in
            let uu____1801 =
              let uu____1808 =
                let uu____1813 =
                  let uu____1814 = e_argv_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____1814 cb a in
                FStar_TypeChecker_NBETerm.as_arg uu____1813 in
              [uu____1808] in
            uu____1792 :: uu____1801 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1785
      | FStar_Reflection_Data.Tv_Abs (b, t) ->
          let uu____1839 =
            let uu____1846 =
              let uu____1851 = FStar_TypeChecker_NBETerm.embed e_binder cb b in
              FStar_TypeChecker_NBETerm.as_arg uu____1851 in
            let uu____1852 =
              let uu____1859 =
                let uu____1864 =
                  let uu____1865 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____1865 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____1864 in
              [uu____1859] in
            uu____1846 :: uu____1852 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1839
      | FStar_Reflection_Data.Tv_Arrow (b, c) ->
          let uu____1882 =
            let uu____1889 =
              let uu____1894 = FStar_TypeChecker_NBETerm.embed e_binder cb b in
              FStar_TypeChecker_NBETerm.as_arg uu____1894 in
            let uu____1895 =
              let uu____1902 =
                let uu____1907 = FStar_TypeChecker_NBETerm.embed e_comp cb c in
                FStar_TypeChecker_NBETerm.as_arg uu____1907 in
              [uu____1902] in
            uu____1889 :: uu____1895 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1882
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1921 =
            let uu____1928 =
              let uu____1933 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb () in
              FStar_TypeChecker_NBETerm.as_arg uu____1933 in
            [uu____1928] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1921
      | FStar_Reflection_Data.Tv_Refine (bv, t) ->
          let uu____1944 =
            let uu____1951 =
              let uu____1956 = FStar_TypeChecker_NBETerm.embed e_bv cb bv in
              FStar_TypeChecker_NBETerm.as_arg uu____1956 in
            let uu____1957 =
              let uu____1964 =
                let uu____1969 =
                  let uu____1970 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____1970 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____1969 in
              [uu____1964] in
            uu____1951 :: uu____1957 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1944
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1986 =
            let uu____1993 =
              let uu____1998 = FStar_TypeChecker_NBETerm.embed e_const cb c in
              FStar_TypeChecker_NBETerm.as_arg uu____1998 in
            [uu____1993] in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1986
      | FStar_Reflection_Data.Tv_Uvar (u, d) ->
          let uu____2009 =
            let uu____2016 =
              let uu____2021 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u in
              FStar_TypeChecker_NBETerm.as_arg uu____2021 in
            let uu____2022 =
              let uu____2029 =
                let uu____2034 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar in
                FStar_TypeChecker_NBETerm.as_arg uu____2034 in
              [uu____2029] in
            uu____2016 :: uu____2022 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____2009
      | FStar_Reflection_Data.Tv_Let (r, attrs, b, t1, t2) ->
          let uu____2060 =
            let uu____2067 =
              let uu____2072 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r in
              FStar_TypeChecker_NBETerm.as_arg uu____2072 in
            let uu____2073 =
              let uu____2080 =
                let uu____2085 =
                  let uu____2086 = FStar_TypeChecker_NBETerm.e_list e_term in
                  FStar_TypeChecker_NBETerm.embed uu____2086 cb attrs in
                FStar_TypeChecker_NBETerm.as_arg uu____2085 in
              let uu____2093 =
                let uu____2100 =
                  let uu____2105 = FStar_TypeChecker_NBETerm.embed e_bv cb b in
                  FStar_TypeChecker_NBETerm.as_arg uu____2105 in
                let uu____2106 =
                  let uu____2113 =
                    let uu____2118 =
                      let uu____2119 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.embed uu____2119 cb t1 in
                    FStar_TypeChecker_NBETerm.as_arg uu____2118 in
                  let uu____2122 =
                    let uu____2129 =
                      let uu____2134 =
                        let uu____2135 = e_term_aq aq in
                        FStar_TypeChecker_NBETerm.embed uu____2135 cb t2 in
                      FStar_TypeChecker_NBETerm.as_arg uu____2134 in
                    [uu____2129] in
                  uu____2113 :: uu____2122 in
                uu____2100 :: uu____2106 in
              uu____2080 :: uu____2093 in
            uu____2067 :: uu____2073 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____2060
      | FStar_Reflection_Data.Tv_Match (t, brs) ->
          let uu____2168 =
            let uu____2175 =
              let uu____2180 =
                let uu____2181 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____2181 cb t in
              FStar_TypeChecker_NBETerm.as_arg uu____2180 in
            let uu____2184 =
              let uu____2191 =
                let uu____2196 =
                  let uu____2197 =
                    let uu____2206 = e_branch_aq aq in
                    FStar_TypeChecker_NBETerm.e_list uu____2206 in
                  FStar_TypeChecker_NBETerm.embed uu____2197 cb brs in
                FStar_TypeChecker_NBETerm.as_arg uu____2196 in
              [uu____2191] in
            uu____2175 :: uu____2184 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2168
      | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
          let uu____2242 =
            let uu____2249 =
              let uu____2254 =
                let uu____2255 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____2255 cb e in
              FStar_TypeChecker_NBETerm.as_arg uu____2254 in
            let uu____2258 =
              let uu____2265 =
                let uu____2270 =
                  let uu____2271 = e_term_aq aq in
                  FStar_TypeChecker_NBETerm.embed uu____2271 cb t in
                FStar_TypeChecker_NBETerm.as_arg uu____2270 in
              let uu____2274 =
                let uu____2281 =
                  let uu____2286 =
                    let uu____2287 =
                      let uu____2292 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.e_option uu____2292 in
                    FStar_TypeChecker_NBETerm.embed uu____2287 cb tacopt in
                  FStar_TypeChecker_NBETerm.as_arg uu____2286 in
                [uu____2281] in
              uu____2265 :: uu____2274 in
            uu____2249 :: uu____2258 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2242
      | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
          let uu____2320 =
            let uu____2327 =
              let uu____2332 =
                let uu____2333 = e_term_aq aq in
                FStar_TypeChecker_NBETerm.embed uu____2333 cb e in
              FStar_TypeChecker_NBETerm.as_arg uu____2332 in
            let uu____2336 =
              let uu____2343 =
                let uu____2348 = FStar_TypeChecker_NBETerm.embed e_comp cb c in
                FStar_TypeChecker_NBETerm.as_arg uu____2348 in
              let uu____2349 =
                let uu____2356 =
                  let uu____2361 =
                    let uu____2362 =
                      let uu____2367 = e_term_aq aq in
                      FStar_TypeChecker_NBETerm.e_option uu____2367 in
                    FStar_TypeChecker_NBETerm.embed uu____2362 cb tacopt in
                  FStar_TypeChecker_NBETerm.as_arg uu____2361 in
                [uu____2356] in
              uu____2343 :: uu____2349 in
            uu____2327 :: uu____2336 in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2320
      | FStar_Reflection_Data.Tv_Unknown ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            [] in
    let unembed_term_view cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2408, (b, uu____2410)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2429 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu____2429
            (fun b1 ->
               FStar_All.pipe_left
                 (fun uu____2436 -> FStar_Pervasives_Native.Some uu____2436)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2438, (b, uu____2440)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2459 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu____2459
            (fun b1 ->
               FStar_All.pipe_left
                 (fun uu____2466 -> FStar_Pervasives_Native.Some uu____2466)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2468, (f, uu____2470)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2489 = FStar_TypeChecker_NBETerm.unembed e_fv cb f in
          FStar_Util.bind_opt uu____2489
            (fun f1 ->
               FStar_All.pipe_left
                 (fun uu____2496 -> FStar_Pervasives_Native.Some uu____2496)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2498, (r, uu____2500)::(l, uu____2502)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2525 = FStar_TypeChecker_NBETerm.unembed e_term cb l in
          FStar_Util.bind_opt uu____2525
            (fun l1 ->
               let uu____2531 = FStar_TypeChecker_NBETerm.unembed e_argv cb r in
               FStar_Util.bind_opt uu____2531
                 (fun r1 ->
                    FStar_All.pipe_left
                      (fun uu____2538 ->
                         FStar_Pervasives_Native.Some uu____2538)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2540, (t1, uu____2542)::(b, uu____2544)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2567 = FStar_TypeChecker_NBETerm.unembed e_binder cb b in
          FStar_Util.bind_opt uu____2567
            (fun b1 ->
               let uu____2573 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____2573
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun uu____2580 ->
                         FStar_Pervasives_Native.Some uu____2580)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2582, (t1, uu____2584)::(b, uu____2586)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2609 = FStar_TypeChecker_NBETerm.unembed e_binder cb b in
          FStar_Util.bind_opt uu____2609
            (fun b1 ->
               let uu____2615 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1 in
               FStar_Util.bind_opt uu____2615
                 (fun c ->
                    FStar_All.pipe_left
                      (fun uu____2622 ->
                         FStar_Pervasives_Native.Some uu____2622)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2624, (u, uu____2626)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2645 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u in
          FStar_Util.bind_opt uu____2645
            (fun u1 ->
               FStar_All.pipe_left
                 (fun uu____2652 -> FStar_Pervasives_Native.Some uu____2652)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2654, (t1, uu____2656)::(b, uu____2658)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2681 = FStar_TypeChecker_NBETerm.unembed e_bv cb b in
          FStar_Util.bind_opt uu____2681
            (fun b1 ->
               let uu____2687 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____2687
                 (fun t2 ->
                    FStar_All.pipe_left
                      (fun uu____2694 ->
                         FStar_Pervasives_Native.Some uu____2694)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2696, (c, uu____2698)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2717 = FStar_TypeChecker_NBETerm.unembed e_const cb c in
          FStar_Util.bind_opt uu____2717
            (fun c1 ->
               FStar_All.pipe_left
                 (fun uu____2724 -> FStar_Pervasives_Native.Some uu____2724)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2726, (l, uu____2728)::(u, uu____2730)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2753 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u in
          FStar_Util.bind_opt uu____2753
            (fun u1 ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l in
               FStar_All.pipe_left
                 (fun uu____2762 -> FStar_Pervasives_Native.Some uu____2762)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2764,
           (t2, uu____2766)::(t1, uu____2768)::(b, uu____2770)::(attrs,
                                                                 uu____2772)::
           (r, uu____2774)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2809 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r in
          FStar_Util.bind_opt uu____2809
            (fun r1 ->
               let uu____2815 =
                 let uu____2820 = FStar_TypeChecker_NBETerm.e_list e_term in
                 FStar_TypeChecker_NBETerm.unembed uu____2820 cb attrs in
               FStar_Util.bind_opt uu____2815
                 (fun attrs1 ->
                    let uu____2834 =
                      FStar_TypeChecker_NBETerm.unembed e_bv cb b in
                    FStar_Util.bind_opt uu____2834
                      (fun b1 ->
                         let uu____2840 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                         FStar_Util.bind_opt uu____2840
                           (fun t11 ->
                              let uu____2846 =
                                FStar_TypeChecker_NBETerm.unembed e_term cb
                                  t2 in
                              FStar_Util.bind_opt uu____2846
                                (fun t21 ->
                                   FStar_All.pipe_left
                                     (fun uu____2853 ->
                                        FStar_Pervasives_Native.Some
                                          uu____2853)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, attrs1, b1, t11, t21)))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2857, (brs, uu____2859)::(t1, uu____2861)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2884 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
          FStar_Util.bind_opt uu____2884
            (fun t2 ->
               let uu____2890 =
                 let uu____2895 = FStar_TypeChecker_NBETerm.e_list e_branch in
                 FStar_TypeChecker_NBETerm.unembed uu____2895 cb brs in
               FStar_Util.bind_opt uu____2890
                 (fun brs1 ->
                    FStar_All.pipe_left
                      (fun uu____2910 ->
                         FStar_Pervasives_Native.Some uu____2910)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2914,
           (tacopt, uu____2916)::(t1, uu____2918)::(e, uu____2920)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2947 = FStar_TypeChecker_NBETerm.unembed e_term cb e in
          FStar_Util.bind_opt uu____2947
            (fun e1 ->
               let uu____2953 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStar_Util.bind_opt uu____2953
                 (fun t2 ->
                    let uu____2959 =
                      let uu____2964 =
                        FStar_TypeChecker_NBETerm.e_option e_term in
                      FStar_TypeChecker_NBETerm.unembed uu____2964 cb tacopt in
                    FStar_Util.bind_opt uu____2959
                      (fun tacopt1 ->
                         FStar_All.pipe_left
                           (fun uu____2979 ->
                              FStar_Pervasives_Native.Some uu____2979)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv, uu____2983,
           (tacopt, uu____2985)::(c, uu____2987)::(e, uu____2989)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____3016 = FStar_TypeChecker_NBETerm.unembed e_term cb e in
          FStar_Util.bind_opt uu____3016
            (fun e1 ->
               let uu____3022 = FStar_TypeChecker_NBETerm.unembed e_comp cb c in
               FStar_Util.bind_opt uu____3022
                 (fun c1 ->
                    let uu____3028 =
                      let uu____3033 =
                        FStar_TypeChecker_NBETerm.e_option e_term in
                      FStar_TypeChecker_NBETerm.unembed uu____3033 cb tacopt in
                    FStar_Util.bind_opt uu____3028
                      (fun tacopt1 ->
                         FStar_All.pipe_left
                           (fun uu____3048 ->
                              FStar_Pervasives_Native.Some uu____3048)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv, uu____3052, []) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun uu____3069 -> FStar_Pervasives_Native.Some uu____3069)
            FStar_Reflection_Data.Tv_Unknown
      | uu____3070 ->
          ((let uu____3072 =
              let uu____3077 =
                let uu____3078 = FStar_TypeChecker_NBETerm.t_to_string t in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____3078 in
              (FStar_Errors.Warning_NotEmbedded, uu____3077) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3072);
           FStar_Pervasives_Native.None) in
    mk_emb' embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view_fv
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq []
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view cb bvv =
    let uu____3100 =
      let uu____3107 =
        let uu____3112 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname in
        FStar_TypeChecker_NBETerm.as_arg uu____3112 in
      let uu____3113 =
        let uu____3120 =
          let uu____3125 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index in
          FStar_TypeChecker_NBETerm.as_arg uu____3125 in
        let uu____3126 =
          let uu____3133 =
            let uu____3138 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort in
            FStar_TypeChecker_NBETerm.as_arg uu____3138 in
          [uu____3133] in
        uu____3120 :: uu____3126 in
      uu____3107 :: uu____3113 in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____3100 in
  let unembed_bv_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3171,
         (s, uu____3173)::(idx, uu____3175)::(nm, uu____3177)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____3204 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm in
        FStar_Util.bind_opt uu____3204
          (fun nm1 ->
             let uu____3210 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx in
             FStar_Util.bind_opt uu____3210
               (fun idx1 ->
                  let uu____3216 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s in
                  FStar_Util.bind_opt uu____3216
                    (fun s1 ->
                       FStar_All.pipe_left
                         (fun uu____3223 ->
                            FStar_Pervasives_Native.Some uu____3223)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____3224 ->
        ((let uu____3226 =
            let uu____3231 =
              let uu____3232 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3232 in
            (FStar_Errors.Warning_NotEmbedded, uu____3231) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3226);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t, md) ->
        let uu____3252 =
          let uu____3259 =
            let uu____3264 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu____3264 in
          let uu____3265 =
            let uu____3272 =
              let uu____3277 =
                let uu____3278 = FStar_TypeChecker_NBETerm.e_option e_term in
                FStar_TypeChecker_NBETerm.embed uu____3278 cb md in
              FStar_TypeChecker_NBETerm.as_arg uu____3277 in
            [uu____3272] in
          uu____3259 :: uu____3265 in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3252
    | FStar_Reflection_Data.C_GTotal (t, md) ->
        let uu____3303 =
          let uu____3310 =
            let uu____3315 = FStar_TypeChecker_NBETerm.embed e_term cb t in
            FStar_TypeChecker_NBETerm.as_arg uu____3315 in
          let uu____3316 =
            let uu____3323 =
              let uu____3328 =
                let uu____3329 = FStar_TypeChecker_NBETerm.e_option e_term in
                FStar_TypeChecker_NBETerm.embed uu____3329 cb md in
              FStar_TypeChecker_NBETerm.as_arg uu____3328 in
            [uu____3323] in
          uu____3310 :: uu____3316 in
        mkConstruct
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.fv []
          uu____3303
    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
        let uu____3351 =
          let uu____3358 =
            let uu____3363 = FStar_TypeChecker_NBETerm.embed e_term cb pre in
            FStar_TypeChecker_NBETerm.as_arg uu____3363 in
          let uu____3364 =
            let uu____3371 =
              let uu____3376 = FStar_TypeChecker_NBETerm.embed e_term cb post in
              FStar_TypeChecker_NBETerm.as_arg uu____3376 in
            let uu____3377 =
              let uu____3384 =
                let uu____3389 =
                  FStar_TypeChecker_NBETerm.embed e_term cb pats in
                FStar_TypeChecker_NBETerm.as_arg uu____3389 in
              [uu____3384] in
            uu____3371 :: uu____3377 in
          uu____3358 :: uu____3364 in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3351
    | FStar_Reflection_Data.C_Eff (us, eff, res, args) ->
        let uu____3418 =
          let uu____3425 =
            let uu____3430 =
              let uu____3431 =
                FStar_TypeChecker_NBETerm.e_list
                  FStar_TypeChecker_NBETerm.e_unit in
              FStar_TypeChecker_NBETerm.embed uu____3431 cb us in
            FStar_TypeChecker_NBETerm.as_arg uu____3430 in
          let uu____3438 =
            let uu____3445 =
              let uu____3450 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_string_list cb eff in
              FStar_TypeChecker_NBETerm.as_arg uu____3450 in
            let uu____3453 =
              let uu____3460 =
                let uu____3465 =
                  FStar_TypeChecker_NBETerm.embed e_term cb res in
                FStar_TypeChecker_NBETerm.as_arg uu____3465 in
              let uu____3466 =
                let uu____3473 =
                  let uu____3478 =
                    let uu____3479 = FStar_TypeChecker_NBETerm.e_list e_argv in
                    FStar_TypeChecker_NBETerm.embed uu____3479 cb args in
                  FStar_TypeChecker_NBETerm.as_arg uu____3478 in
                [uu____3473] in
              uu____3460 :: uu____3466 in
            uu____3445 :: uu____3453 in
          uu____3425 :: uu____3438 in
        mkConstruct FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.fv
          [] uu____3418 in
  let unembed_comp_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3522, (md, uu____3524)::(t1, uu____3526)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3549 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu____3549
          (fun t2 ->
             let uu____3555 =
               let uu____3560 = FStar_TypeChecker_NBETerm.e_option e_term in
               FStar_TypeChecker_NBETerm.unembed uu____3560 cb md in
             FStar_Util.bind_opt uu____3555
               (fun md1 ->
                  FStar_All.pipe_left
                    (fun uu____3575 ->
                       FStar_Pervasives_Native.Some uu____3575)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3579, (md, uu____3581)::(t1, uu____3583)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
        ->
        let uu____3606 = FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStar_Util.bind_opt uu____3606
          (fun t2 ->
             let uu____3612 =
               let uu____3617 = FStar_TypeChecker_NBETerm.e_option e_term in
               FStar_TypeChecker_NBETerm.unembed uu____3617 cb md in
             FStar_Util.bind_opt uu____3612
               (fun md1 ->
                  FStar_All.pipe_left
                    (fun uu____3632 ->
                       FStar_Pervasives_Native.Some uu____3632)
                    (FStar_Reflection_Data.C_GTotal (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3636,
         (post, uu____3638)::(pre, uu____3640)::(pats, uu____3642)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3669 = FStar_TypeChecker_NBETerm.unembed e_term cb pre in
        FStar_Util.bind_opt uu____3669
          (fun pre1 ->
             let uu____3675 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post in
             FStar_Util.bind_opt uu____3675
               (fun post1 ->
                  let uu____3681 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb pats in
                  FStar_Util.bind_opt uu____3681
                    (fun pats1 ->
                       FStar_All.pipe_left
                         (fun uu____3688 ->
                            FStar_Pervasives_Native.Some uu____3688)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1, pats1)))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____3690,
         (args, uu____3692)::(res, uu____3694)::(eff, uu____3696)::(us,
                                                                    uu____3698)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
        ->
        let uu____3729 =
          let uu____3734 =
            FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_unit in
          FStar_TypeChecker_NBETerm.unembed uu____3734 cb us in
        FStar_Util.bind_opt uu____3729
          (fun us1 ->
             let uu____3748 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_string_list cb eff in
             FStar_Util.bind_opt uu____3748
               (fun eff1 ->
                  let uu____3762 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb res in
                  FStar_Util.bind_opt uu____3762
                    (fun res1 ->
                       let uu____3768 =
                         let uu____3773 =
                           FStar_TypeChecker_NBETerm.e_list e_argv in
                         FStar_TypeChecker_NBETerm.unembed uu____3773 cb args in
                       FStar_Util.bind_opt uu____3768
                         (fun args1 ->
                            FStar_All.pipe_left
                              (fun uu____3788 ->
                                 FStar_Pervasives_Native.Some uu____3788)
                              (FStar_Reflection_Data.C_Eff
                                 (us1, eff1, res1, args1))))))
    | uu____3793 ->
        ((let uu____3795 =
            let uu____3800 =
              let uu____3801 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3801 in
            (FStar_Errors.Warning_NotEmbedded, uu____3800) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3795);
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
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3843, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3859, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____3875, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____3890 ->
        ((let uu____3892 =
            let uu____3897 =
              let uu____3898 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded order: %s" uu____3898 in
            (FStar_Errors.Warning_NotEmbedded, uu____3897) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3892);
         FStar_Pervasives_Native.None) in
  let uu____3899 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  mk_emb' embed_order unembed_order uu____3899
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
           FStar_Syntax_Syntax.ltyp = uu____3929;
           FStar_Syntax_Syntax.rng = uu____3930;_},
         uu____3931)
        ->
        let uu____3950 = FStar_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu____3950
    | uu____3951 ->
        ((let uu____3953 =
            let uu____3958 =
              let uu____3959 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3959 in
            (FStar_Errors.Warning_NotEmbedded, uu____3958) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3953);
         FStar_Pervasives_Native.None) in
  mk_emb' embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt_fv
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string in
  let embed_ident cb i =
    let uu____3982 =
      let uu____3987 = FStar_Ident.range_of_id i in
      let uu____3988 = FStar_Ident.string_of_id i in (uu____3987, uu____3988) in
    FStar_TypeChecker_NBETerm.embed repr cb uu____3982 in
  let unembed_ident cb t =
    let uu____4008 = FStar_TypeChecker_NBETerm.unembed repr cb t in
    match uu____4008 with
    | FStar_Pervasives_Native.Some (rng, s) ->
        let uu____4027 = FStar_Ident.mk_ident (s, rng) in
        FStar_Pervasives_Native.Some uu____4027
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let range_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  let string_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
  let et =
    let uu____4035 =
      let uu____4042 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2 in
      let uu____4043 =
        let uu____4046 = fv_as_emb_typ range_fv in
        let uu____4047 =
          let uu____4050 = fv_as_emb_typ string_fv in [uu____4050] in
        uu____4046 :: uu____4047 in
      (uu____4042, uu____4043) in
    FStar_Syntax_Syntax.ET_app uu____4035 in
  let uu____4053 =
    let uu____4054 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    let uu____4055 =
      let uu____4062 =
        let uu____4067 = mkFV range_fv [] [] in
        FStar_TypeChecker_NBETerm.as_arg uu____4067 in
      let uu____4072 =
        let uu____4079 =
          let uu____4084 = mkFV string_fv [] [] in
          FStar_TypeChecker_NBETerm.as_arg uu____4084 in
        [uu____4079] in
      uu____4062 :: uu____4072 in
    mkFV uu____4054 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____4055 in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____4053 et
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
    | FStar_Reflection_Data.Sg_Let (r, fv, univs, ty, t) ->
        let uu____4133 =
          let uu____4140 =
            let uu____4145 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r in
            FStar_TypeChecker_NBETerm.as_arg uu____4145 in
          let uu____4146 =
            let uu____4153 =
              let uu____4158 = FStar_TypeChecker_NBETerm.embed e_fv cb fv in
              FStar_TypeChecker_NBETerm.as_arg uu____4158 in
            let uu____4159 =
              let uu____4166 =
                let uu____4171 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs in
                FStar_TypeChecker_NBETerm.as_arg uu____4171 in
              let uu____4174 =
                let uu____4181 =
                  let uu____4186 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty in
                  FStar_TypeChecker_NBETerm.as_arg uu____4186 in
                let uu____4187 =
                  let uu____4194 =
                    let uu____4199 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t in
                    FStar_TypeChecker_NBETerm.as_arg uu____4199 in
                  [uu____4194] in
                uu____4181 :: uu____4187 in
              uu____4166 :: uu____4174 in
            uu____4153 :: uu____4159 in
          uu____4140 :: uu____4146 in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____4133
    | FStar_Reflection_Data.Sg_Constructor (nm, ty) ->
        let uu____4226 =
          let uu____4233 =
            let uu____4238 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm in
            FStar_TypeChecker_NBETerm.as_arg uu____4238 in
          let uu____4241 =
            let uu____4248 =
              let uu____4253 = FStar_TypeChecker_NBETerm.embed e_term cb ty in
              FStar_TypeChecker_NBETerm.as_arg uu____4253 in
            [uu____4248] in
          uu____4233 :: uu____4241 in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____4226
    | FStar_Reflection_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu____4283 =
          let uu____4290 =
            let uu____4295 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm in
            FStar_TypeChecker_NBETerm.as_arg uu____4295 in
          let uu____4298 =
            let uu____4305 =
              let uu____4310 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs in
              FStar_TypeChecker_NBETerm.as_arg uu____4310 in
            let uu____4313 =
              let uu____4320 =
                let uu____4325 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs in
                FStar_TypeChecker_NBETerm.as_arg uu____4325 in
              let uu____4326 =
                let uu____4333 =
                  let uu____4338 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t in
                  FStar_TypeChecker_NBETerm.as_arg uu____4338 in
                let uu____4339 =
                  let uu____4346 =
                    let uu____4351 =
                      let uu____4352 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list in
                      FStar_TypeChecker_NBETerm.embed uu____4352 cb dcs in
                    FStar_TypeChecker_NBETerm.as_arg uu____4351 in
                  [uu____4346] in
                uu____4333 :: uu____4339 in
              uu____4320 :: uu____4326 in
            uu____4305 :: uu____4313 in
          uu____4290 :: uu____4298 in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____4283
    | FStar_Reflection_Data.Unk ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          [] in
  let unembed_sigelt_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4409,
         (dcs, uu____4411)::(t1, uu____4413)::(bs, uu____4415)::(us,
                                                                 uu____4417)::
         (nm, uu____4419)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____4454 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm in
        FStar_Util.bind_opt uu____4454
          (fun nm1 ->
             let uu____4468 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us in
             FStar_Util.bind_opt uu____4468
               (fun us1 ->
                  let uu____4482 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs in
                  FStar_Util.bind_opt uu____4482
                    (fun bs1 ->
                       let uu____4488 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                       FStar_Util.bind_opt uu____4488
                         (fun t2 ->
                            let uu____4494 =
                              let uu____4501 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list in
                              FStar_TypeChecker_NBETerm.unembed uu____4501 cb
                                dcs in
                            FStar_Util.bind_opt uu____4494
                              (fun dcs1 ->
                                 FStar_All.pipe_left
                                   (fun uu____4526 ->
                                      FStar_Pervasives_Native.Some uu____4526)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4534,
         (t1, uu____4536)::(ty, uu____4538)::(univs, uu____4540)::(fvar,
                                                                   uu____4542)::
         (r, uu____4544)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____4579 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r in
        FStar_Util.bind_opt uu____4579
          (fun r1 ->
             let uu____4585 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar in
             FStar_Util.bind_opt uu____4585
               (fun fvar1 ->
                  let uu____4591 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs in
                  FStar_Util.bind_opt uu____4591
                    (fun univs1 ->
                       let uu____4605 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty in
                       FStar_Util.bind_opt uu____4605
                         (fun ty1 ->
                            let uu____4611 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1 in
                            FStar_Util.bind_opt uu____4611
                              (fun t2 ->
                                 FStar_All.pipe_left
                                   (fun uu____4618 ->
                                      FStar_Pervasives_Native.Some uu____4618)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar1, univs1, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____4622, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4637 ->
        ((let uu____4639 =
            let uu____4644 =
              let uu____4645 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4645 in
            (FStar_Errors.Warning_NotEmbedded, uu____4644) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4639);
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
        let uu____4664 =
          let uu____4671 =
            let uu____4676 =
              FStar_TypeChecker_NBETerm.mk_t
                (FStar_TypeChecker_NBETerm.Constant
                   (FStar_TypeChecker_NBETerm.Int i)) in
            FStar_TypeChecker_NBETerm.as_arg uu____4676 in
          [uu____4671] in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4664
    | FStar_Reflection_Data.Mult (e1, e2) ->
        let uu____4687 =
          let uu____4694 =
            let uu____4699 = embed_exp cb e1 in
            FStar_TypeChecker_NBETerm.as_arg uu____4699 in
          let uu____4700 =
            let uu____4707 =
              let uu____4712 = embed_exp cb e2 in
              FStar_TypeChecker_NBETerm.as_arg uu____4712 in
            [uu____4707] in
          uu____4694 :: uu____4700 in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4687 in
  let rec unembed_exp cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct (fv, uu____4741, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4757, (i, uu____4759)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____4778 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i in
        FStar_Util.bind_opt uu____4778
          (fun i1 ->
             FStar_All.pipe_left
               (fun uu____4785 -> FStar_Pervasives_Native.Some uu____4785)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, uu____4787, (e2, uu____4789)::(e1, uu____4791)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____4814 = unembed_exp cb e1 in
        FStar_Util.bind_opt uu____4814
          (fun e11 ->
             let uu____4820 = unembed_exp cb e2 in
             FStar_Util.bind_opt uu____4820
               (fun e21 ->
                  FStar_All.pipe_left
                    (fun uu____4827 ->
                       FStar_Pervasives_Native.Some uu____4827)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____4828 ->
        ((let uu____4830 =
            let uu____4835 =
              let uu____4836 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4836 in
            (FStar_Errors.Warning_NotEmbedded, uu____4835) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4830);
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
    let uu____4858 = FStar_Ident.path_of_lid lid in
    FStar_TypeChecker_NBETerm.embed e_string_list rng uu____4858 in
  let unembed cb t =
    let uu____4878 = FStar_TypeChecker_NBETerm.unembed e_string_list cb t in
    FStar_Util.map_opt uu____4878
      (fun p -> FStar_Ident.lid_of_path p FStar_Range.dummyRange) in
  let uu____4891 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] [] in
  let uu____4896 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed unembed uu____4891 uu____4896
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
        let uu____4979 =
          let uu____4986 =
            let uu____4991 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu____4991 in
          [uu____4986] in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.fv
          [] uu____4979
    | FStar_Reflection_Data.Discriminator l ->
        let uu____5001 =
          let uu____5008 =
            let uu____5013 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu____5013 in
          [uu____5008] in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.fv
          [] uu____5001
    | FStar_Reflection_Data.Action l ->
        let uu____5023 =
          let uu____5030 =
            let uu____5035 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu____5035 in
          [uu____5030] in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.fv []
          uu____5023
    | FStar_Reflection_Data.Projector (l, i) ->
        let uu____5046 =
          let uu____5053 =
            let uu____5058 = FStar_TypeChecker_NBETerm.embed e_lid cb l in
            FStar_TypeChecker_NBETerm.as_arg uu____5058 in
          let uu____5059 =
            let uu____5066 =
              let uu____5071 = FStar_TypeChecker_NBETerm.embed e_ident cb i in
              FStar_TypeChecker_NBETerm.as_arg uu____5071 in
            [uu____5066] in
          uu____5053 :: uu____5059 in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.fv
          [] uu____5046
    | FStar_Reflection_Data.RecordType (ids1, ids2) ->
        let uu____5094 =
          let uu____5101 =
            let uu____5106 =
              let uu____5107 = FStar_TypeChecker_NBETerm.e_list e_ident in
              FStar_TypeChecker_NBETerm.embed uu____5107 cb ids1 in
            FStar_TypeChecker_NBETerm.as_arg uu____5106 in
          let uu____5114 =
            let uu____5121 =
              let uu____5126 =
                let uu____5127 = FStar_TypeChecker_NBETerm.e_list e_ident in
                FStar_TypeChecker_NBETerm.embed uu____5127 cb ids2 in
              FStar_TypeChecker_NBETerm.as_arg uu____5126 in
            [uu____5121] in
          uu____5101 :: uu____5114 in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.fv
          [] uu____5094
    | FStar_Reflection_Data.RecordConstructor (ids1, ids2) ->
        let uu____5156 =
          let uu____5163 =
            let uu____5168 =
              let uu____5169 = FStar_TypeChecker_NBETerm.e_list e_ident in
              FStar_TypeChecker_NBETerm.embed uu____5169 cb ids1 in
            FStar_TypeChecker_NBETerm.as_arg uu____5168 in
          let uu____5176 =
            let uu____5183 =
              let uu____5188 =
                let uu____5189 = FStar_TypeChecker_NBETerm.e_list e_ident in
                FStar_TypeChecker_NBETerm.embed uu____5189 cb ids2 in
              FStar_TypeChecker_NBETerm.as_arg uu____5188 in
            [uu____5183] in
          uu____5163 :: uu____5176 in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.fv
          [] uu____5156 in
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
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (l, uu____5446)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
        ->
        let uu____5463 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
        FStar_Util.bind_opt uu____5463
          (fun l1 ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Reflectable l1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (l, uu____5470)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
        ->
        let uu____5487 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
        FStar_Util.bind_opt uu____5487
          (fun l1 ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Discriminator l1))
    | FStar_TypeChecker_NBETerm.Construct (fv, [], (l, uu____5494)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
        ->
        let uu____5511 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
        FStar_Util.bind_opt uu____5511
          (fun l1 ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Action l1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, [], (i, uu____5518)::(l, uu____5520)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
        ->
        let uu____5541 = FStar_TypeChecker_NBETerm.unembed e_ident cb i in
        FStar_Util.bind_opt uu____5541
          (fun i1 ->
             let uu____5547 = FStar_TypeChecker_NBETerm.unembed e_lid cb l in
             FStar_Util.bind_opt uu____5547
               (fun l1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Projector (l1, i1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, [], (ids2, uu____5554)::(ids1, uu____5556)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
        ->
        let uu____5577 =
          let uu____5582 = FStar_TypeChecker_NBETerm.e_list e_ident in
          FStar_TypeChecker_NBETerm.unembed uu____5582 cb ids1 in
        FStar_Util.bind_opt uu____5577
          (fun ids11 ->
             let uu____5596 =
               let uu____5601 = FStar_TypeChecker_NBETerm.e_list e_ident in
               FStar_TypeChecker_NBETerm.unembed uu____5601 cb ids2 in
             FStar_Util.bind_opt uu____5596
               (fun ids21 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordType (ids11, ids21))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv, [], (ids2, uu____5620)::(ids1, uu____5622)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
        ->
        let uu____5643 =
          let uu____5648 = FStar_TypeChecker_NBETerm.e_list e_ident in
          FStar_TypeChecker_NBETerm.unembed uu____5648 cb ids1 in
        FStar_Util.bind_opt uu____5643
          (fun ids11 ->
             let uu____5662 =
               let uu____5667 = FStar_TypeChecker_NBETerm.e_list e_ident in
               FStar_TypeChecker_NBETerm.unembed uu____5667 cb ids2 in
             FStar_Util.bind_opt uu____5662
               (fun ids21 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordConstructor (ids11, ids21))))
    | uu____5684 ->
        ((let uu____5686 =
            let uu____5691 =
              let uu____5692 = FStar_TypeChecker_NBETerm.t_to_string t in
              FStar_Util.format1 "Not an embedded qualifier: %s" uu____5692 in
            (FStar_Errors.Warning_NotEmbedded, uu____5691) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5686);
         FStar_Pervasives_Native.None) in
  let uu____5693 =
    mkConstruct FStar_Reflection_Data.fstar_refl_qualifier_fv [] [] in
  let uu____5698 =
    fv_as_emb_typ FStar_Reflection_Data.fstar_refl_qualifier_fv in
  FStar_TypeChecker_NBETerm.mk_emb embed unembed uu____5693 uu____5698
let (e_qualifiers :
  FStar_Reflection_Data.qualifier Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_qualifier