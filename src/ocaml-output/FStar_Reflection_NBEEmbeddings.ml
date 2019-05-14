open Prims
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
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
      (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv  ->
    fun us  ->
      fun ts  ->
        FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us)
          (FStar_List.rev ts)
  
let (fv_as_emb_typ : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.emb_typ) =
  fun fv  ->
    let uu____95 =
      let uu____103 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____103, [])  in
    FStar_Syntax_Syntax.ET_app uu____95
  
let mk_emb' :
  'Auu____121 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____121 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____121 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____121 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____192 = mkFV fv [] []  in
        let uu____197 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____192 uu____197
  
let mk_lazy :
  'Auu____209 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____209 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____259 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____259;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____265  ->
                 let uu____266 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____266)
             in
          FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk1)
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv cb bv =
    mk_lazy cb bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv
     in
  let unembed_bv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
           FStar_Syntax_Syntax.ltyp = uu____380;
           FStar_Syntax_Syntax.rng = uu____381;_},uu____382)
        ->
        let uu____413 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _446  -> FStar_Pervasives_Native.Some _446)
          uu____413
    | uu____447 ->
        ((let uu____449 =
            let uu____455 =
              let uu____457 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____457  in
            (FStar_Errors.Warning_NotEmbedded, uu____455)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____449);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv_fv 
let (e_binder :
  FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding) =
  let embed_binder cb b =
    mk_lazy cb b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder
     in
  let unembed_binder cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
           FStar_Syntax_Syntax.ltyp = uu____524;
           FStar_Syntax_Syntax.rng = uu____525;_},uu____526)
        ->
        let uu____557 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____557
    | uu____558 ->
        ((let uu____560 =
            let uu____566 =
              let uu____568 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____568  in
            (FStar_Errors.Warning_NotEmbedded, uu____566)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____560);
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
          let uu____618 = f x  in
          FStar_Util.bind_opt uu____618
            (fun x1  ->
               let uu____626 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____626
                 (fun xs1  -> FStar_Pervasives_Native.Some (x1 :: xs1)))
  
let (e_term_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
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
      | uu____787 -> FStar_Pervasives_Native.None  in
    let uu____792 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____797 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____792;
      FStar_TypeChecker_NBETerm.emb_typ = uu____797
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
        let uu____873 =
          let uu____880 =
            let uu____885 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____885  in
          [uu____880]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____873
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____961)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____984 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____984
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____1005 ->
        ((let uu____1007 =
            let uu____1013 =
              let uu____1015 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____1015  in
            (FStar_Errors.Warning_NotEmbedded, uu____1013)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1007);
         FStar_Pervasives_Native.None)
     in
  let uu____1019 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____1024 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____1019
    uu____1024
  
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_list e_binder 
let (e_fv : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding) =
  let embed_fv cb fv =
    mk_lazy cb fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar
     in
  let unembed_fv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
           FStar_Syntax_Syntax.ltyp = uu____1106;
           FStar_Syntax_Syntax.rng = uu____1107;_},uu____1108)
        ->
        let uu____1139 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____1139
    | uu____1152 ->
        ((let uu____1154 =
            let uu____1160 =
              let uu____1162 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____1162  in
            (FStar_Errors.Warning_NotEmbedded, uu____1160)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1154);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv_fv 
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp cb c =
    mk_lazy cb c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp
     in
  let unembed_comp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
           FStar_Syntax_Syntax.ltyp = uu____1249;
           FStar_Syntax_Syntax.rng = uu____1250;_},uu____1251)
        ->
        let uu____1282 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____1282
    | uu____1299 ->
        ((let uu____1301 =
            let uu____1307 =
              let uu____1309 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____1309  in
            (FStar_Errors.Warning_NotEmbedded, uu____1307)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1301);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp_fv 
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env cb e =
    mk_lazy cb e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env
     in
  let unembed_env cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
           FStar_Syntax_Syntax.ltyp = uu____1698;
           FStar_Syntax_Syntax.rng = uu____1699;_},uu____1700)
        ->
        let uu____1731 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____1731
    | uu____1948 ->
        ((let uu____1950 =
            let uu____1956 =
              let uu____1958 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____1958  in
            (FStar_Errors.Warning_NotEmbedded, uu____1956)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1950);
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
        let uu____2112 =
          let uu____2119 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____2119]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____2112
    | FStar_Reflection_Data.C_String s ->
        let uu____2134 =
          let uu____2141 =
            let uu____2146 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2146  in
          [uu____2141]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____2134
    | FStar_Reflection_Data.C_Range r ->
        let uu____2157 =
          let uu____2164 =
            let uu____2169 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2169  in
          [uu____2164]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____2157
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____2183 =
          let uu____2190 =
            let uu____2195 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2195  in
          [uu____2190]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____2183
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____2289)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____2312 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____2312
          (fun i1  ->
             FStar_All.pipe_left
               (fun _2319  -> FStar_Pervasives_Native.Some _2319)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____2322)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____2345 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____2345
          (fun s1  ->
             FStar_All.pipe_left
               (fun _2356  -> FStar_Pervasives_Native.Some _2356)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____2359)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____2382 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____2382
          (fun r1  ->
             FStar_All.pipe_left
               (fun _2389  -> FStar_Pervasives_Native.Some _2389)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____2411)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____2434 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____2434
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _2453  -> FStar_Pervasives_Native.Some _2453)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____2454 ->
        ((let uu____2456 =
            let uu____2462 =
              let uu____2464 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____2464  in
            (FStar_Errors.Warning_NotEmbedded, uu____2462)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2456);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____2482  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____2503 =
            let uu____2510 =
              let uu____2515 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2515  in
            [uu____2510]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____2503
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____2536 =
            let uu____2543 =
              let uu____2548 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____2548  in
            let uu____2552 =
              let uu____2559 =
                let uu____2564 =
                  let uu____2565 =
                    let uu____2577 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____2577  in
                  FStar_TypeChecker_NBETerm.embed uu____2565 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____2564  in
              [uu____2559]  in
            uu____2543 :: uu____2552  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____2536
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____2607 =
            let uu____2614 =
              let uu____2619 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____2619  in
            [uu____2614]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____2607
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____2639 =
            let uu____2646 =
              let uu____2651 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____2651  in
            [uu____2646]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____2639
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____2685 =
            let uu____2692 =
              let uu____2697 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____2697  in
            let uu____2703 =
              let uu____2710 =
                let uu____2715 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2715  in
              [uu____2710]  in
            uu____2692 :: uu____2703  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____2685
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____2757)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____2780 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____2780
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _2787  -> FStar_Pervasives_Native.Some _2787)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____2790)::(f,uu____2792)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____2819 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____2819
            (fun f1  ->
               let uu____2837 =
                 let uu____2842 =
                   let uu____2854 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____2854  in
                 FStar_TypeChecker_NBETerm.unembed uu____2842 cb ps  in
               FStar_Util.bind_opt uu____2837
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _2874  -> FStar_Pervasives_Native.Some _2874)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____2882)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____2905 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____2905
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _2932  -> FStar_Pervasives_Native.Some _2932)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____2935)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____2958 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____2958
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _2985  -> FStar_Pervasives_Native.Some _2985)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____2988)::(bv,uu____2990)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____3017 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____3017
            (fun bv1  ->
               let uu____3043 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____3043
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _3066  -> FStar_Pervasives_Native.Some _3066)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____3076 ->
          ((let uu____3078 =
              let uu____3084 =
                let uu____3086 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____3086
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3084)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3078);
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
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____3185 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____3185
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____3260 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____3260 e_aqualv
  
let rec unlazy_as_t :
  'Auu____3285 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____3285
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____3298;
             FStar_Syntax_Syntax.rng = uu____3299;_},uu____3300)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____3331 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____3405 =
            let uu____3412 =
              let uu____3417 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3417  in
            [uu____3412]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____3405
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____3435 =
            let uu____3442 =
              let uu____3447 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3447  in
            [uu____3442]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____3435
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____3467 =
            let uu____3474 =
              let uu____3479 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3479  in
            [uu____3474]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____3467
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____3503 =
            let uu____3510 =
              let uu____3515 =
                let uu____3516 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____3516 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3515  in
            let uu____3534 =
              let uu____3541 =
                let uu____3546 =
                  let uu____3547 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____3547 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____3546  in
              [uu____3541]  in
            uu____3510 :: uu____3534  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____3503
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____3595 =
            let uu____3602 =
              let uu____3607 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3607  in
            let uu____3608 =
              let uu____3615 =
                let uu____3620 =
                  let uu____3621 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____3621 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____3620  in
              [uu____3615]  in
            uu____3602 :: uu____3608  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____3595
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____3661 =
            let uu____3668 =
              let uu____3673 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3673  in
            let uu____3674 =
              let uu____3681 =
                let uu____3686 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____3686  in
              [uu____3681]  in
            uu____3668 :: uu____3674  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____3661
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____3704 =
            let uu____3711 =
              let uu____3716 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3716  in
            [uu____3711]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____3704
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____3745 =
            let uu____3752 =
              let uu____3757 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3757  in
            let uu____3763 =
              let uu____3770 =
                let uu____3775 =
                  let uu____3776 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____3776 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____3775  in
              [uu____3770]  in
            uu____3752 :: uu____3763  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____3745
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____3807 =
            let uu____3814 =
              let uu____3819 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3819  in
            [uu____3814]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____3807
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____3830 =
            let uu____3837 =
              let uu____3842 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3842  in
            let uu____3843 =
              let uu____3850 =
                let uu____3855 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____3855  in
              [uu____3850]  in
            uu____3837 :: uu____3843  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____3830
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____3904 =
            let uu____3911 =
              let uu____3916 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3916  in
            let uu____3918 =
              let uu____3925 =
                let uu____3930 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____3930  in
              let uu____3936 =
                let uu____3943 =
                  let uu____3948 =
                    let uu____3949 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____3949 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____3948  in
                let uu____3967 =
                  let uu____3974 =
                    let uu____3979 =
                      let uu____3980 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____3980 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____3979  in
                  [uu____3974]  in
                uu____3943 :: uu____3967  in
              uu____3925 :: uu____3936  in
            uu____3911 :: uu____3918  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____3904
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____4032 =
            let uu____4039 =
              let uu____4044 =
                let uu____4045 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____4045 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____4044  in
            let uu____4063 =
              let uu____4070 =
                let uu____4075 =
                  let uu____4076 =
                    let uu____4096 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____4096  in
                  FStar_TypeChecker_NBETerm.embed uu____4076 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____4075  in
              [uu____4070]  in
            uu____4039 :: uu____4063  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____4032
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____4175 =
            let uu____4182 =
              let uu____4187 =
                let uu____4188 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____4188 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____4187  in
            let uu____4206 =
              let uu____4213 =
                let uu____4218 =
                  let uu____4219 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____4219 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____4218  in
              let uu____4237 =
                let uu____4244 =
                  let uu____4249 =
                    let uu____4250 =
                      let uu____4266 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____4266  in
                    FStar_TypeChecker_NBETerm.embed uu____4250 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4249  in
                [uu____4244]  in
              uu____4213 :: uu____4237  in
            uu____4182 :: uu____4206  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____4175
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____4337 =
            let uu____4344 =
              let uu____4349 =
                let uu____4350 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____4350 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____4349  in
            let uu____4368 =
              let uu____4375 =
                let uu____4380 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____4380  in
              let uu____4385 =
                let uu____4392 =
                  let uu____4397 =
                    let uu____4398 =
                      let uu____4414 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____4414  in
                    FStar_TypeChecker_NBETerm.embed uu____4398 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4397  in
                [uu____4392]  in
              uu____4375 :: uu____4385  in
            uu____4344 :: uu____4368  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____4337
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____4482,(b,uu____4484)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____4509 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____4509
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _4536  -> FStar_Pervasives_Native.Some _4536)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____4538,(b,uu____4540)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____4565 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____4565
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _4592  -> FStar_Pervasives_Native.Some _4592)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____4594,(f,uu____4596)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____4621 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____4621
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _4640  -> FStar_Pervasives_Native.Some _4640)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____4642,(r,uu____4644)::(l,uu____4646)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____4675 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____4675
            (fun l1  ->
               let uu____4697 = FStar_TypeChecker_NBETerm.unembed e_argv cb r
                  in
               FStar_Util.bind_opt uu____4697
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _4704  -> FStar_Pervasives_Native.Some _4704)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____4710,(t1,uu____4712)::(b,uu____4714)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____4743 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____4743
            (fun b1  ->
               let uu____4749 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____4749
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _4772  -> FStar_Pervasives_Native.Some _4772)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____4778,(t1,uu____4780)::(b,uu____4782)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____4811 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____4811
            (fun b1  ->
               let uu____4817 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____4817
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _4840  -> FStar_Pervasives_Native.Some _4840)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____4846,(u,uu____4848)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____4873 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____4873
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _4880  -> FStar_Pervasives_Native.Some _4880)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____4882,(t1,uu____4884)::(b,uu____4886)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____4915 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____4915
            (fun b1  ->
               let uu____4941 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____4941
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _4964  -> FStar_Pervasives_Native.Some _4964)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____4975,(c,uu____4977)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____5002 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____5002
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _5009  -> FStar_Pervasives_Native.Some _5009)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____5011,(l,uu____5013)::(u,uu____5015)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____5044 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____5044
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _5053  -> FStar_Pervasives_Native.Some _5053)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____5055,(t2,uu____5057)::(t1,uu____5059)::(b,uu____5061)::
           (r,uu____5063)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____5100 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____5100
            (fun r1  ->
               let uu____5110 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____5110
                 (fun b1  ->
                    let uu____5136 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____5136
                      (fun t11  ->
                         let uu____5158 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____5158
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _5181  ->
                                   FStar_Pervasives_Native.Some _5181)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____5197,(brs,uu____5199)::(t1,uu____5201)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____5230 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
          FStar_Util.bind_opt uu____5230
            (fun t2  ->
               let uu____5252 =
                 let uu____5257 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____5257 cb brs  in
               FStar_Util.bind_opt uu____5252
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _5279  -> FStar_Pervasives_Native.Some _5279)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____5287,(tacopt,uu____5289)::(t1,uu____5291)::(e,uu____5293)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____5326 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____5326
            (fun e1  ->
               let uu____5348 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____5348
                 (fun t2  ->
                    let uu____5370 =
                      let uu____5379 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____5379 cb tacopt
                       in
                    FStar_Util.bind_opt uu____5370
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _5421  -> FStar_Pervasives_Native.Some _5421)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____5437,(tacopt,uu____5439)::(c,uu____5441)::(e,uu____5443)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____5476 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____5476
            (fun e1  ->
               let uu____5498 = FStar_TypeChecker_NBETerm.unembed e_comp cb c
                  in
               FStar_Util.bind_opt uu____5498
                 (fun c1  ->
                    let uu____5520 =
                      let uu____5529 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____5529 cb tacopt
                       in
                    FStar_Util.bind_opt uu____5520
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _5571  -> FStar_Pervasives_Native.Some _5571)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____5587,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _5610  -> FStar_Pervasives_Native.Some _5610)
            FStar_Reflection_Data.Tv_Unknown
      | uu____5611 ->
          ((let uu____5613 =
              let uu____5619 =
                let uu____5621 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____5621
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5619)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____5613);
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
    let uu____5688 =
      let uu____5695 =
        let uu____5700 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____5700  in
      let uu____5702 =
        let uu____5709 =
          let uu____5714 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____5714  in
        let uu____5715 =
          let uu____5722 =
            let uu____5727 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____5727  in
          [uu____5722]  in
        uu____5709 :: uu____5715  in
      uu____5695 :: uu____5702  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____5688
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____5778,(s,uu____5780)::(idx,uu____5782)::(nm,uu____5784)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____5817 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____5817
          (fun nm1  ->
             let uu____5830 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____5830
               (fun idx1  ->
                  let uu____5839 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____5839
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _5874  -> FStar_Pervasives_Native.Some _5874)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____5875 ->
        ((let uu____5877 =
            let uu____5883 =
              let uu____5885 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____5885  in
            (FStar_Errors.Warning_NotEmbedded, uu____5883)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5877);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____5946 =
          let uu____5953 =
            let uu____5958 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____5958  in
          let uu____5963 =
            let uu____5970 =
              let uu____5975 =
                let uu____5976 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____5976 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____5975  in
            [uu____5970]  in
          uu____5953 :: uu____5963  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____5946
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____6043 =
          let uu____6050 =
            let uu____6055 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____6055  in
          let uu____6060 =
            let uu____6067 =
              let uu____6072 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____6072  in
            [uu____6067]  in
          uu____6050 :: uu____6060  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____6043
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____6117,(md,uu____6119)::(t1,uu____6121)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____6150 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____6150
          (fun t2  ->
             let uu____6172 =
               let uu____6181 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____6181 cb md  in
             FStar_Util.bind_opt uu____6172
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _6223  -> FStar_Pervasives_Native.Some _6223)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____6235,(post,uu____6237)::(pre,uu____6239)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____6268 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____6268
          (fun pre1  ->
             let uu____6290 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____6290
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _6313  -> FStar_Pervasives_Native.Some _6313)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____6323,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _6346  -> FStar_Pervasives_Native.Some _6346)
          FStar_Reflection_Data.C_Unknown
    | uu____6347 ->
        ((let uu____6349 =
            let uu____6355 =
              let uu____6357 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____6357
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6355)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6349);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____6426,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____6448,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____6470,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____6491 ->
        ((let uu____6493 =
            let uu____6499 =
              let uu____6501 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____6501  in
            (FStar_Errors.Warning_NotEmbedded, uu____6499)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6493);
         FStar_Pervasives_Native.None)
     in
  let uu____6505 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____6505 
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt cb se =
    mk_lazy cb se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt
     in
  let unembed_sigelt cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
           FStar_Syntax_Syntax.ltyp = uu____6595;
           FStar_Syntax_Syntax.rng = uu____6596;_},uu____6597)
        ->
        let uu____6628 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____6628
    | uu____6649 ->
        ((let uu____6651 =
            let uu____6657 =
              let uu____6659 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____6659  in
            (FStar_Errors.Warning_NotEmbedded, uu____6657)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6651);
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
    let uu____6735 =
      let uu____6741 = FStar_Ident.range_of_id i  in
      let uu____6742 = FStar_Ident.text_of_id i  in (uu____6741, uu____6742)
       in
    FStar_TypeChecker_NBETerm.embed repr cb uu____6735  in
  let unembed_ident cb t =
    let uu____6777 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____6777 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____6803 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____6803
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
    let uu____6833 =
      let uu____6841 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____6843 =
        let uu____6846 = fv_as_emb_typ range_fv  in
        let uu____6847 =
          let uu____6850 = fv_as_emb_typ string_fv  in [uu____6850]  in
        uu____6846 :: uu____6847  in
      (uu____6841, uu____6843)  in
    FStar_Syntax_Syntax.ET_app uu____6833  in
  let uu____6854 =
    let uu____6855 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____6862 =
      let uu____6869 =
        let uu____6874 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____6874  in
      let uu____6879 =
        let uu____6886 =
          let uu____6891 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____6891  in
        [uu____6886]  in
      uu____6869 :: uu____6879  in
    mkFV uu____6855 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____6862
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____6854 et 
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
        let uu____7018 =
          let uu____7025 =
            let uu____7030 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____7030  in
          let uu____7032 =
            let uu____7039 =
              let uu____7044 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____7044  in
            let uu____7048 =
              let uu____7055 =
                let uu____7060 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____7060  in
              let uu____7065 =
                let uu____7072 =
                  let uu____7077 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____7077  in
                let uu____7082 =
                  let uu____7089 =
                    let uu____7094 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____7094  in
                  [uu____7089]  in
                uu____7072 :: uu____7082  in
              uu____7055 :: uu____7065  in
            uu____7039 :: uu____7048  in
          uu____7025 :: uu____7032  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____7018
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____7133 =
          let uu____7140 =
            let uu____7145 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____7145  in
          let uu____7149 =
            let uu____7156 =
              let uu____7161 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____7161  in
            [uu____7156]  in
          uu____7140 :: uu____7149  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____7133
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____7207 =
          let uu____7214 =
            let uu____7219 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____7219  in
          let uu____7223 =
            let uu____7230 =
              let uu____7235 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____7235  in
            let uu____7240 =
              let uu____7247 =
                let uu____7252 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____7252  in
              let uu____7253 =
                let uu____7260 =
                  let uu____7265 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____7265  in
                let uu____7270 =
                  let uu____7277 =
                    let uu____7282 =
                      let uu____7283 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____7283 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____7282  in
                  [uu____7277]  in
                uu____7260 :: uu____7270  in
              uu____7247 :: uu____7253  in
            uu____7230 :: uu____7240  in
          uu____7214 :: uu____7223  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____7207
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____7358,(dcs,uu____7360)::(t1,uu____7362)::(bs,uu____7364)::
         (us,uu____7366)::(nm,uu____7368)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____7409 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____7409
          (fun nm1  ->
             let uu____7427 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____7427
               (fun us1  ->
                  let uu____7449 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____7449
                    (fun bs1  ->
                       let uu____7455 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____7455
                         (fun t2  ->
                            let uu____7477 =
                              let uu____7485 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____7485 cb
                                dcs
                               in
                            FStar_Util.bind_opt uu____7477
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _7522  ->
                                      FStar_Pervasives_Native.Some _7522)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____7536,(t1,uu____7538)::(ty,uu____7540)::(univs1,uu____7542)::
         (fvar1,uu____7544)::(r,uu____7546)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____7587 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____7587
          (fun r1  ->
             let uu____7597 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1
                in
             FStar_Util.bind_opt uu____7597
               (fun fvar2  ->
                  let uu____7615 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____7615
                    (fun univs2  ->
                       let uu____7637 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____7637
                         (fun ty1  ->
                            let uu____7659 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____7659
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _7682  ->
                                      FStar_Pervasives_Native.Some _7682)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____7700,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____7721 ->
        ((let uu____7723 =
            let uu____7729 =
              let uu____7731 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____7731
               in
            (FStar_Errors.Warning_NotEmbedded, uu____7729)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____7723);
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
        let uu____7769 =
          let uu____7776 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____7776]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____7769
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____7791 =
          let uu____7798 =
            let uu____7803 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____7803  in
          let uu____7804 =
            let uu____7811 =
              let uu____7816 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____7816  in
            [uu____7811]  in
          uu____7798 :: uu____7804  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____7791
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____7853,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____7875,(i,uu____7877)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____7902 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____7902
          (fun i1  ->
             FStar_All.pipe_left
               (fun _7909  -> FStar_Pervasives_Native.Some _7909)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____7911,(e2,uu____7913)::(e1,uu____7915)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____7944 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____7944
          (fun e11  ->
             let uu____7950 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____7950
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _7957  -> FStar_Pervasives_Native.Some _7957)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____7958 ->
        ((let uu____7960 =
            let uu____7966 =
              let uu____7968 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____7968  in
            (FStar_Errors.Warning_NotEmbedded, uu____7966)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____7960);
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