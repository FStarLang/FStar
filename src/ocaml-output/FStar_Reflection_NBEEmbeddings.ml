open Prims
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv  ->
    fun us  ->
      fun ts  ->
        FStar_TypeChecker_NBETerm.mkFV fv (FStar_List.rev us)
          (FStar_List.rev ts)
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv  ->
    fun us  ->
      fun ts  ->
        FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us)
          (FStar_List.rev ts)
  
let (fv_as_emb_typ : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.emb_typ) =
  fun fv  ->
    let uu____76 =
      let uu____83 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____83, [])  in
    FStar_Syntax_Syntax.ET_app uu____76
  
let mk_emb' :
  'Auu____94 .
    (FStar_TypeChecker_NBETerm.iapp_cb ->
       'Auu____94 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.iapp_cb ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____94 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____94 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____152 = mkFV fv [] []  in
        let uu____157 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____152 uu____157
  
let mk_lazy :
  'Auu____166 .
    'Auu____166 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun obj  ->
    fun ty  ->
      fun kind  ->
        let li =
          let uu____187 = FStar_Dyn.mkdyn obj  in
          {
            FStar_Syntax_Syntax.blob = uu____187;
            FStar_Syntax_Syntax.lkind = kind;
            FStar_Syntax_Syntax.ltyp = ty;
            FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
          }  in
        FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl li)
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv cb bv =
    mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv
     in
  let unembed_bv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____245;
          FStar_Syntax_Syntax.rng = uu____246;_})
        ->
        let uu____257 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____257
    | uu____260 ->
        ((let uu____262 =
            let uu____267 =
              let uu____268 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____268  in
            (FStar_Errors.Warning_NotEmbedded, uu____267)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____262);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv_fv 
let (e_binder :
  FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding) =
  let embed_binder cb b =
    mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder
     in
  let unembed_binder cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____318;
          FStar_Syntax_Syntax.rng = uu____319;_})
        ->
        let uu____330 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____330
    | uu____331 ->
        ((let uu____333 =
            let uu____338 =
              let uu____339 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____339  in
            (FStar_Errors.Warning_NotEmbedded, uu____338)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____333);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_binder unembed_binder
    FStar_Reflection_Data.fstar_refl_binder_fv
  
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
          let uu____385 = f x  in
          FStar_Util.bind_opt uu____385
            (fun x1  ->
               let uu____393 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____393
                 (fun xs1  -> FStar_Pervasives_Native.Some (x1 :: xs1)))
  
let (e_term_aq :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term cb t =
      let qi =
        {
          FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
          FStar_Syntax_Syntax.antiquotes = aq
        }  in
      FStar_TypeChecker_NBETerm.Quote (t, qi)  in
    let rec unembed_term cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Quote (tm,qi) ->
          FStar_Pervasives_Native.Some tm
      | uu____482 -> FStar_Pervasives_Native.None  in
    let uu____483 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____488 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____483;
      FStar_TypeChecker_NBETerm.emb_typ = uu____488
    }
  
let (e_term : FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding) =
  e_term_aq [] 
let (e_aqualv :
  FStar_Reflection_Data.aqualv FStar_TypeChecker_NBETerm.embedding) =
  let embed_aqualv cb q =
    match q with
    | FStar_Reflection_Data.Q_Explicit  ->
        mkConstruct
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Q_Implicit  ->
        mkConstruct
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Q_Meta t ->
        let uu____529 =
          let uu____536 =
            let uu____541 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____541  in
          [uu____536]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____529
     in
  let unembed_aqualv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____607)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____624 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____624
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____633 ->
        ((let uu____635 =
            let uu____640 =
              let uu____641 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____641  in
            (FStar_Errors.Warning_NotEmbedded, uu____640)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____635);
         FStar_Pervasives_Native.None)
     in
  let uu____642 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____647 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____642
    uu____647
  
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_list e_binder 
let (e_fv : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding) =
  let embed_fv cb fv =
    mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar
     in
  let unembed_fv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____699;
          FStar_Syntax_Syntax.rng = uu____700;_})
        ->
        let uu____711 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____711
    | uu____712 ->
        ((let uu____714 =
            let uu____719 =
              let uu____720 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____720  in
            (FStar_Errors.Warning_NotEmbedded, uu____719)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____714);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv_fv 
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp cb c =
    mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp
     in
  let unembed_comp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____770;
          FStar_Syntax_Syntax.rng = uu____771;_})
        ->
        let uu____782 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____782
    | uu____783 ->
        ((let uu____785 =
            let uu____790 =
              let uu____791 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____791  in
            (FStar_Errors.Warning_NotEmbedded, uu____790)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____785);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp_fv 
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env cb e =
    mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env
     in
  let unembed_env cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____841;
          FStar_Syntax_Syntax.rng = uu____842;_})
        ->
        let uu____853 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____853
    | uu____854 ->
        ((let uu____856 =
            let uu____861 =
              let uu____862 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____862  in
            (FStar_Errors.Warning_NotEmbedded, uu____861)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____856);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_env unembed_env FStar_Reflection_Data.fstar_refl_env_fv 
let (e_const :
  FStar_Reflection_Data.vconst FStar_TypeChecker_NBETerm.embedding) =
  let embed_const cb c =
    match c with
    | FStar_Reflection_Data.C_Unit  ->
        mkConstruct FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.C_True  ->
        mkConstruct FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.C_False  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Int i ->
        let uu____899 =
          let uu____906 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____906]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____899
    | FStar_Reflection_Data.C_String s ->
        let uu____920 =
          let uu____927 =
            let uu____932 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____932  in
          [uu____927]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____920
     in
  let unembed_const cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____1011)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____1028 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____1028
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____1041)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____1058 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1058
          (fun s1  ->
             FStar_All.pipe_left
               (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
               (FStar_Reflection_Data.C_String s1))
    | uu____1069 ->
        ((let uu____1071 =
            let uu____1076 =
              let uu____1077 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____1077  in
            (FStar_Errors.Warning_NotEmbedded, uu____1076)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1071);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____1084  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1107 =
            let uu____1114 =
              let uu____1119 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1119  in
            [uu____1114]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____1107
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1138 =
            let uu____1145 =
              let uu____1150 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1150  in
            let uu____1155 =
              let uu____1162 =
                let uu____1167 =
                  let uu____1168 =
                    let uu____1173 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____1173  in
                  FStar_TypeChecker_NBETerm.embed uu____1168 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____1167  in
              [uu____1162]  in
            uu____1145 :: uu____1155  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1138
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1195 =
            let uu____1202 =
              let uu____1207 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1207  in
            [uu____1202]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1195
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1221 =
            let uu____1228 =
              let uu____1233 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1233  in
            [uu____1228]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1221
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1248 =
            let uu____1255 =
              let uu____1260 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1260  in
            let uu____1265 =
              let uu____1272 =
                let uu____1277 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1277  in
              [uu____1272]  in
            uu____1255 :: uu____1265  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1248
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____1321)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1338 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____1338
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____1351)::(f,uu____1353)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1374 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____1374
            (fun f1  ->
               let uu____1384 =
                 let uu____1389 =
                   let uu____1394 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____1394  in
                 FStar_TypeChecker_NBETerm.unembed uu____1389 cb ps  in
               FStar_Util.bind_opt uu____1384
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1415)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1432 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1432
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1445)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1462 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1462
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____1475)::(bv,uu____1477)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1498 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1498
            (fun bv1  ->
               let uu____1508 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____1508
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1519 ->
          ((let uu____1521 =
              let uu____1526 =
                let uu____1527 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1527
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1526)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1521);
           FStar_Pervasives_Native.None)
       in
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
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1561 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1561
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1591 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1591 e_aqualv
  
let rec unlazy_as_t :
  'Auu____1600 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1600
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____1613;
            FStar_Syntax_Syntax.rng = uu____1614;_})
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1625 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1671 =
            let uu____1678 =
              let uu____1683 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1683  in
            [uu____1678]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1671
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1697 =
            let uu____1704 =
              let uu____1709 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1709  in
            [uu____1704]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1697
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1723 =
            let uu____1730 =
              let uu____1735 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1735  in
            [uu____1730]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1723
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1750 =
            let uu____1757 =
              let uu____1762 =
                let uu____1763 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1763 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1762  in
            let uu____1770 =
              let uu____1777 =
                let uu____1782 =
                  let uu____1783 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1783 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1782  in
              [uu____1777]  in
            uu____1757 :: uu____1770  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1750
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1812 =
            let uu____1819 =
              let uu____1824 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1824  in
            let uu____1829 =
              let uu____1836 =
                let uu____1841 =
                  let uu____1842 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1842 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1841  in
              [uu____1836]  in
            uu____1819 :: uu____1829  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1812
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1863 =
            let uu____1870 =
              let uu____1875 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1875  in
            let uu____1880 =
              let uu____1887 =
                let uu____1892 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1892  in
              [uu____1887]  in
            uu____1870 :: uu____1880  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1863
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1910 =
            let uu____1917 =
              let uu____1922 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1922  in
            [uu____1917]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1910
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____1937 =
            let uu____1944 =
              let uu____1949 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1949  in
            let uu____1954 =
              let uu____1961 =
                let uu____1966 =
                  let uu____1967 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1967 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1966  in
              [uu____1961]  in
            uu____1944 :: uu____1954  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1937
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1987 =
            let uu____1994 =
              let uu____1999 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1999  in
            [uu____1994]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1987
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2014 =
            let uu____2021 =
              let uu____2026 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2026  in
            let uu____2031 =
              let uu____2038 =
                let uu____2043 =
                  mk_lazy (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2043  in
              [uu____2038]  in
            uu____2021 :: uu____2031  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____2014
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2064 =
            let uu____2071 =
              let uu____2076 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2076  in
            let uu____2081 =
              let uu____2088 =
                let uu____2093 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2093  in
              let uu____2098 =
                let uu____2105 =
                  let uu____2110 =
                    let uu____2111 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____2111 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2110  in
                let uu____2118 =
                  let uu____2125 =
                    let uu____2130 =
                      let uu____2131 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____2131 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____2130  in
                  [uu____2125]  in
                uu____2105 :: uu____2118  in
              uu____2088 :: uu____2098  in
            uu____2071 :: uu____2081  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____2064
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____2164 =
            let uu____2171 =
              let uu____2176 =
                let uu____2177 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2177 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____2176  in
            let uu____2184 =
              let uu____2191 =
                let uu____2196 =
                  let uu____2197 =
                    let uu____2206 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____2206  in
                  FStar_TypeChecker_NBETerm.embed uu____2197 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2196  in
              [uu____2191]  in
            uu____2171 :: uu____2184  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2164
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____2246 =
            let uu____2253 =
              let uu____2258 =
                let uu____2259 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2259 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2258  in
            let uu____2266 =
              let uu____2273 =
                let uu____2278 =
                  let uu____2279 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2279 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2278  in
              let uu____2286 =
                let uu____2293 =
                  let uu____2298 =
                    let uu____2299 =
                      let uu____2304 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2304  in
                    FStar_TypeChecker_NBETerm.embed uu____2299 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2298  in
                [uu____2293]  in
              uu____2273 :: uu____2286  in
            uu____2253 :: uu____2266  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2246
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2336 =
            let uu____2343 =
              let uu____2348 =
                let uu____2349 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2349 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2348  in
            let uu____2356 =
              let uu____2363 =
                let uu____2368 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2368  in
              let uu____2373 =
                let uu____2380 =
                  let uu____2385 =
                    let uu____2386 =
                      let uu____2391 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2391  in
                    FStar_TypeChecker_NBETerm.embed uu____2386 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2385  in
                [uu____2380]  in
              uu____2363 :: uu____2373  in
            uu____2343 :: uu____2356  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2336
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2446,(b,uu____2448)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2467 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2467
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2479,(b,uu____2481)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2500 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2500
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2512,(f,uu____2514)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2533 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____2533
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2545,(r,uu____2547)::(l,uu____2549)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2572 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____2572
            (fun l1  ->
               let uu____2582 = FStar_TypeChecker_NBETerm.unembed e_argv cb r
                  in
               FStar_Util.bind_opt uu____2582
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2594,(t1,uu____2596)::(b,uu____2598)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2621 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2621
            (fun b1  ->
               let uu____2631 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2631
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2643,(t1,uu____2645)::(b,uu____2647)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2670 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2670
            (fun b1  ->
               let uu____2680 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____2680
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2692,(u,uu____2694)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2713 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____2713
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2725,(t1,uu____2727)::(b,uu____2729)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2752 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2752
            (fun b1  ->
               let uu____2762 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2762
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2774,(c,uu____2776)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2795 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____2795
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2807,(l,uu____2809)::(u,uu____2811)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2834 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____2834
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2848,(t2,uu____2850)::(t1,uu____2852)::(b,uu____2854)::
           (r,uu____2856)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2887 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____2887
            (fun r1  ->
               let uu____2897 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____2897
                 (fun b1  ->
                    let uu____2907 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____2907
                      (fun t11  ->
                         let uu____2917 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____2917
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _0_34  ->
                                   FStar_Pervasives_Native.Some _0_34)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2929,(brs,uu____2931)::(t1,uu____2933)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2956 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
          FStar_Util.bind_opt uu____2956
            (fun t2  ->
               let uu____2966 =
                 let uu____2971 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2971 cb brs  in
               FStar_Util.bind_opt uu____2966
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2993,(tacopt,uu____2995)::(t1,uu____2997)::(e,uu____2999)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____3026 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____3026
            (fun e1  ->
               let uu____3036 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____3036
                 (fun t2  ->
                    let uu____3046 =
                      let uu____3051 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3051 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3046
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____3073,(tacopt,uu____3075)::(c,uu____3077)::(e,uu____3079)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____3106 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____3106
            (fun e1  ->
               let uu____3116 = FStar_TypeChecker_NBETerm.unembed e_comp cb c
                  in
               FStar_Util.bind_opt uu____3116
                 (fun c1  ->
                    let uu____3126 =
                      let uu____3131 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3131 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3126
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____3153,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
            FStar_Reflection_Data.Tv_Unknown
      | uu____3170 ->
          ((let uu____3172 =
              let uu____3177 =
                let uu____3178 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____3178
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3177)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3172);
           FStar_Pervasives_Native.None)
       in
    mk_emb' embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view_fv
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view cb bvv =
    let uu____3210 =
      let uu____3217 =
        let uu____3222 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____3222  in
      let uu____3227 =
        let uu____3234 =
          let uu____3239 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____3239  in
        let uu____3244 =
          let uu____3251 =
            let uu____3256 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3256  in
          [uu____3251]  in
        uu____3234 :: uu____3244  in
      uu____3217 :: uu____3227  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____3210
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3303,(s,uu____3305)::(idx,uu____3307)::(nm,uu____3309)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____3336 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____3336
          (fun nm1  ->
             let uu____3346 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____3346
               (fun idx1  ->
                  let uu____3356 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____3356
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____3367 ->
        ((let uu____3369 =
            let uu____3374 =
              let uu____3375 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3375  in
            (FStar_Errors.Warning_NotEmbedded, uu____3374)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3369);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____3405 =
          let uu____3412 =
            let uu____3417 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3417  in
          let uu____3422 =
            let uu____3429 =
              let uu____3434 =
                let uu____3435 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____3435 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3434  in
            [uu____3429]  in
          uu____3412 :: uu____3422  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3405
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3463 =
          let uu____3470 =
            let uu____3475 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3475  in
          let uu____3480 =
            let uu____3487 =
              let uu____3492 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3492  in
            [uu____3487]  in
          uu____3470 :: uu____3480  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3463
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3539,(md,uu____3541)::(t1,uu____3543)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3566 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3566
          (fun t2  ->
             let uu____3576 =
               let uu____3581 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3581 cb md  in
             FStar_Util.bind_opt uu____3576
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3603,(post,uu____3605)::(pre,uu____3607)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3630 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____3630
          (fun pre1  ->
             let uu____3640 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____3640
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3652,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
          FStar_Reflection_Data.C_Unknown
    | uu____3669 ->
        ((let uu____3671 =
            let uu____3676 =
              let uu____3677 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3677
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3676)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3671);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_comp_view unembed_comp_view
    FStar_Reflection_Data.fstar_refl_comp_view_fv
  
let (e_order : FStar_Order.order FStar_TypeChecker_NBETerm.embedding) =
  let embed_order cb o =
    match o with
    | FStar_Order.Lt  -> mkConstruct FStar_Reflection_Data.ord_Lt_fv [] []
    | FStar_Order.Eq  -> mkConstruct FStar_Reflection_Data.ord_Eq_fv [] []
    | FStar_Order.Gt  -> mkConstruct FStar_Reflection_Data.ord_Gt_fv [] []
     in
  let unembed_order cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3739,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3755,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3771,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____3786 ->
        ((let uu____3788 =
            let uu____3793 =
              let uu____3794 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____3794  in
            (FStar_Errors.Warning_NotEmbedded, uu____3793)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3788);
         FStar_Pervasives_Native.None)
     in
  let uu____3795 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____3795 
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt cb se =
    mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt
     in
  let unembed_sigelt cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____3845;
          FStar_Syntax_Syntax.rng = uu____3846;_})
        ->
        let uu____3857 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____3857
    | uu____3858 ->
        ((let uu____3860 =
            let uu____3865 =
              let uu____3866 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3866  in
            (FStar_Errors.Warning_NotEmbedded, uu____3865)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3860);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt_fv
  
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string
     in
  let embed_ident cb i =
    let uu____3899 =
      let uu____3904 = FStar_Ident.range_of_id i  in
      let uu____3905 = FStar_Ident.text_of_id i  in (uu____3904, uu____3905)
       in
    FStar_TypeChecker_NBETerm.embed repr cb uu____3899  in
  let unembed_ident cb t =
    let uu____3939 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____3939 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____3962 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____3962
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let range_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  let string_fv =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  let et =
    let uu____3970 =
      let uu____3977 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____3978 =
        let uu____3981 = fv_as_emb_typ range_fv  in
        let uu____3982 =
          let uu____3985 = fv_as_emb_typ string_fv  in [uu____3985]  in
        uu____3981 :: uu____3982  in
      (uu____3977, uu____3978)  in
    FStar_Syntax_Syntax.ET_app uu____3970  in
  let uu____3988 =
    let uu____3989 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____3990 =
      let uu____3997 =
        let uu____4002 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____4002  in
      let uu____4007 =
        let uu____4014 =
          let uu____4019 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____4019  in
        [uu____4014]  in
      uu____3997 :: uu____4007  in
    mkFV uu____3989 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____3990
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3988 et 
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
    | FStar_Reflection_Data.Sg_Let (r,fv,univs1,ty,t) ->
        let uu____4078 =
          let uu____4085 =
            let uu____4090 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____4090  in
          let uu____4095 =
            let uu____4102 =
              let uu____4107 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____4107  in
            let uu____4112 =
              let uu____4119 =
                let uu____4124 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____4124  in
              let uu____4131 =
                let uu____4138 =
                  let uu____4143 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4143  in
                let uu____4148 =
                  let uu____4155 =
                    let uu____4160 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4160  in
                  [uu____4155]  in
                uu____4138 :: uu____4148  in
              uu____4119 :: uu____4131  in
            uu____4102 :: uu____4112  in
          uu____4085 :: uu____4095  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____4078
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4191 =
          let uu____4198 =
            let uu____4203 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4203  in
          let uu____4210 =
            let uu____4217 =
              let uu____4222 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____4222  in
            [uu____4217]  in
          uu____4198 :: uu____4210  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____4191
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____4256 =
          let uu____4263 =
            let uu____4268 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4268  in
          let uu____4275 =
            let uu____4282 =
              let uu____4287 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____4287  in
            let uu____4294 =
              let uu____4301 =
                let uu____4306 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____4306  in
              let uu____4311 =
                let uu____4318 =
                  let uu____4323 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4323  in
                let uu____4328 =
                  let uu____4335 =
                    let uu____4340 =
                      let uu____4341 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____4341 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4340  in
                  [uu____4335]  in
                uu____4318 :: uu____4328  in
              uu____4301 :: uu____4311  in
            uu____4282 :: uu____4294  in
          uu____4263 :: uu____4275  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____4256
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4412,(dcs,uu____4414)::(t1,uu____4416)::(bs,uu____4418)::
         (us,uu____4420)::(nm,uu____4422)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____4457 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____4457
          (fun nm1  ->
             let uu____4475 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____4475
               (fun us1  ->
                  let uu____4493 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____4493
                    (fun bs1  ->
                       let uu____4503 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____4503
                         (fun t2  ->
                            let uu____4513 =
                              let uu____4520 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____4520 cb
                                dcs
                               in
                            FStar_Util.bind_opt uu____4513
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4556,(t1,uu____4558)::(ty,uu____4560)::(univs1,uu____4562)::
         (fvar1,uu____4564)::(r,uu____4566)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____4601 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____4601
          (fun r1  ->
             let uu____4611 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1
                in
             FStar_Util.bind_opt uu____4611
               (fun fvar2  ->
                  let uu____4621 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____4621
                    (fun univs2  ->
                       let uu____4639 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____4639
                         (fun ty1  ->
                            let uu____4649 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____4649
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _0_44  ->
                                      FStar_Pervasives_Native.Some _0_44)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4663,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4678 ->
        ((let uu____4680 =
            let uu____4685 =
              let uu____4686 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4686
               in
            (FStar_Errors.Warning_NotEmbedded, uu____4685)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4680);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_Data.fstar_refl_sigelt_view_fv
  
let (e_exp : FStar_Reflection_Data.exp FStar_TypeChecker_NBETerm.embedding) =
  let rec embed_exp cb e =
    match e with
    | FStar_Reflection_Data.Unit  ->
        mkConstruct FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Var i ->
        let uu____4715 =
          let uu____4722 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____4722]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4715
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____4737 =
          let uu____4744 =
            let uu____4749 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4749  in
          let uu____4756 =
            let uu____4763 =
              let uu____4768 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4768  in
            [uu____4763]  in
          uu____4744 :: uu____4756  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4737
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4813,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4829,(i,uu____4831)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____4850 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____4850
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4862,(e2,uu____4864)::(e1,uu____4866)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____4889 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____4889
          (fun e11  ->
             let uu____4901 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____4901
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____4914 ->
        ((let uu____4916 =
            let uu____4921 =
              let uu____4922 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4922  in
            (FStar_Errors.Warning_NotEmbedded, uu____4921)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4916);
         FStar_Pervasives_Native.None)
     in
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