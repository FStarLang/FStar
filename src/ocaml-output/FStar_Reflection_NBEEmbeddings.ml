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
    let uu____64338 =
      let uu____64346 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____64346, [])  in
    FStar_Syntax_Syntax.ET_app uu____64338
  
let mk_emb' :
  'Auu____64360 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____64360 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____64360 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____64360 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____64402 = mkFV fv [] []  in
        let uu____64407 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____64402 uu____64407
  
let mk_lazy :
  'Auu____64419 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____64419 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____64445 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____64445;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____64451  ->
                 let uu____64452 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____64452)
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
           FStar_Syntax_Syntax.ltyp = uu____64537;
           FStar_Syntax_Syntax.rng = uu____64538;_},uu____64539)
        ->
        let uu____64558 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64561  -> FStar_Pervasives_Native.Some _64561) uu____64558
    | uu____64562 ->
        ((let uu____64564 =
            let uu____64570 =
              let uu____64572 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____64572  in
            (FStar_Errors.Warning_NotEmbedded, uu____64570)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64564);
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
           FStar_Syntax_Syntax.ltyp = uu____64606;
           FStar_Syntax_Syntax.rng = uu____64607;_},uu____64608)
        ->
        let uu____64627 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64627
    | uu____64628 ->
        ((let uu____64630 =
            let uu____64636 =
              let uu____64638 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____64638  in
            (FStar_Errors.Warning_NotEmbedded, uu____64636)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64630);
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
          let uu____64688 = f x  in
          FStar_Util.bind_opt uu____64688
            (fun x1  ->
               let uu____64696 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64696
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
      | uu____64766 -> FStar_Pervasives_Native.None  in
    let uu____64767 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____64772 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____64767;
      FStar_TypeChecker_NBETerm.emb_typ = uu____64772
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
        let uu____64805 =
          let uu____64812 =
            let uu____64817 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____64817  in
          [uu____64812]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____64805
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____64869)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____64886 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____64886
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____64891 ->
        ((let uu____64893 =
            let uu____64899 =
              let uu____64901 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____64901  in
            (FStar_Errors.Warning_NotEmbedded, uu____64899)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64893);
         FStar_Pervasives_Native.None)
     in
  let uu____64905 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____64910 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____64905
    uu____64910
  
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
           FStar_Syntax_Syntax.ltyp = uu____64944;
           FStar_Syntax_Syntax.rng = uu____64945;_},uu____64946)
        ->
        let uu____64965 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64965
    | uu____64966 ->
        ((let uu____64968 =
            let uu____64974 =
              let uu____64976 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____64976  in
            (FStar_Errors.Warning_NotEmbedded, uu____64974)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64968);
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
           FStar_Syntax_Syntax.ltyp = uu____65010;
           FStar_Syntax_Syntax.rng = uu____65011;_},uu____65012)
        ->
        let uu____65031 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65031
    | uu____65032 ->
        ((let uu____65034 =
            let uu____65040 =
              let uu____65042 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____65042  in
            (FStar_Errors.Warning_NotEmbedded, uu____65040)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65034);
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
           FStar_Syntax_Syntax.ltyp = uu____65076;
           FStar_Syntax_Syntax.rng = uu____65077;_},uu____65078)
        ->
        let uu____65097 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65097
    | uu____65098 ->
        ((let uu____65100 =
            let uu____65106 =
              let uu____65108 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____65108  in
            (FStar_Errors.Warning_NotEmbedded, uu____65106)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65100);
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
        let uu____65139 =
          let uu____65146 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____65146]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____65139
    | FStar_Reflection_Data.C_String s ->
        let uu____65161 =
          let uu____65168 =
            let uu____65173 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65173  in
          [uu____65168]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____65161
    | FStar_Reflection_Data.C_Range r ->
        let uu____65184 =
          let uu____65191 =
            let uu____65196 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65196  in
          [uu____65191]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____65184
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____65210 =
          let uu____65217 =
            let uu____65222 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65222  in
          [uu____65217]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____65210
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____65290)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____65307 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____65307
          (fun i1  ->
             FStar_All.pipe_left
               (fun _65314  -> FStar_Pervasives_Native.Some _65314)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____65317)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____65334 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____65334
          (fun s1  ->
             FStar_All.pipe_left
               (fun _65345  -> FStar_Pervasives_Native.Some _65345)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____65348)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____65365 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____65365
          (fun r1  ->
             FStar_All.pipe_left
               (fun _65372  -> FStar_Pervasives_Native.Some _65372)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____65388)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____65405 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____65405
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _65424  -> FStar_Pervasives_Native.Some _65424)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____65425 ->
        ((let uu____65427 =
            let uu____65433 =
              let uu____65435 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____65435  in
            (FStar_Errors.Warning_NotEmbedded, uu____65433)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65427);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____65446  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65459 =
            let uu____65466 =
              let uu____65471 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65471  in
            [uu____65466]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____65459
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65486 =
            let uu____65493 =
              let uu____65498 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65498  in
            let uu____65499 =
              let uu____65506 =
                let uu____65511 =
                  let uu____65512 =
                    let uu____65517 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____65517  in
                  FStar_TypeChecker_NBETerm.embed uu____65512 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____65511  in
              [uu____65506]  in
            uu____65493 :: uu____65499  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____65486
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65535 =
            let uu____65542 =
              let uu____65547 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65547  in
            [uu____65542]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____65535
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65557 =
            let uu____65564 =
              let uu____65569 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65569  in
            [uu____65564]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____65557
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65580 =
            let uu____65587 =
              let uu____65592 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65592  in
            let uu____65593 =
              let uu____65600 =
                let uu____65605 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____65605  in
              [uu____65600]  in
            uu____65587 :: uu____65593  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____65580
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____65635)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____65652 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____65652
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _65659  -> FStar_Pervasives_Native.Some _65659)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____65662)::(f,uu____65664)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____65685 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____65685
            (fun f1  ->
               let uu____65691 =
                 let uu____65696 =
                   let uu____65701 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____65701  in
                 FStar_TypeChecker_NBETerm.unembed uu____65696 cb ps  in
               FStar_Util.bind_opt uu____65691
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _65714  -> FStar_Pervasives_Native.Some _65714)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65719)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____65736 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65736
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65743  -> FStar_Pervasives_Native.Some _65743)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65746)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____65763 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65763
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65770  -> FStar_Pervasives_Native.Some _65770)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____65773)::(bv,uu____65775)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____65796 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65796
            (fun bv1  ->
               let uu____65802 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____65802
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _65809  -> FStar_Pervasives_Native.Some _65809)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____65810 ->
          ((let uu____65812 =
              let uu____65818 =
                let uu____65820 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____65820
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65818)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____65812);
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
    let uu____65861 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____65861
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____65892 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____65892 e_aqualv
  
let rec unlazy_as_t :
  'Auu____65902 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____65902
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____65915;
             FStar_Syntax_Syntax.rng = uu____65916;_},uu____65917)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____65936 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____65974 =
            let uu____65981 =
              let uu____65986 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65986  in
            [uu____65981]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____65974
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____65996 =
            let uu____66003 =
              let uu____66008 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66008  in
            [uu____66003]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____65996
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____66018 =
            let uu____66025 =
              let uu____66030 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66030  in
            [uu____66025]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____66018
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66041 =
            let uu____66048 =
              let uu____66053 =
                let uu____66054 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66054 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____66053  in
            let uu____66057 =
              let uu____66064 =
                let uu____66069 =
                  let uu____66070 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66070 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____66069  in
              [uu____66064]  in
            uu____66048 :: uu____66057  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____66041
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____66095 =
            let uu____66102 =
              let uu____66107 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66107  in
            let uu____66108 =
              let uu____66115 =
                let uu____66120 =
                  let uu____66121 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66121 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66120  in
              [uu____66115]  in
            uu____66102 :: uu____66108  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____66095
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66138 =
            let uu____66145 =
              let uu____66150 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66150  in
            let uu____66151 =
              let uu____66158 =
                let uu____66163 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66163  in
              [uu____66158]  in
            uu____66145 :: uu____66151  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____66138
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66177 =
            let uu____66184 =
              let uu____66189 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66189  in
            [uu____66184]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____66177
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____66200 =
            let uu____66207 =
              let uu____66212 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66212  in
            let uu____66213 =
              let uu____66220 =
                let uu____66225 =
                  let uu____66226 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66226 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66225  in
              [uu____66220]  in
            uu____66207 :: uu____66213  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____66200
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66242 =
            let uu____66249 =
              let uu____66254 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66254  in
            [uu____66249]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____66242
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66265 =
            let uu____66272 =
              let uu____66277 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66277  in
            let uu____66278 =
              let uu____66285 =
                let uu____66290 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66290  in
              [uu____66285]  in
            uu____66272 :: uu____66278  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____66265
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66313 =
            let uu____66320 =
              let uu____66325 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66325  in
            let uu____66327 =
              let uu____66334 =
                let uu____66339 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66339  in
              let uu____66340 =
                let uu____66347 =
                  let uu____66352 =
                    let uu____66353 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____66353 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66352  in
                let uu____66356 =
                  let uu____66363 =
                    let uu____66368 =
                      let uu____66369 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____66369 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____66368  in
                  [uu____66363]  in
                uu____66347 :: uu____66356  in
              uu____66334 :: uu____66340  in
            uu____66320 :: uu____66327  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____66313
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____66398 =
            let uu____66405 =
              let uu____66410 =
                let uu____66411 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66411 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____66410  in
            let uu____66414 =
              let uu____66421 =
                let uu____66426 =
                  let uu____66427 =
                    let uu____66436 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____66436  in
                  FStar_TypeChecker_NBETerm.embed uu____66427 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____66426  in
              [uu____66421]  in
            uu____66405 :: uu____66414  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____66398
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____66472 =
            let uu____66479 =
              let uu____66484 =
                let uu____66485 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66485 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66484  in
            let uu____66488 =
              let uu____66495 =
                let uu____66500 =
                  let uu____66501 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66501 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66500  in
              let uu____66504 =
                let uu____66511 =
                  let uu____66516 =
                    let uu____66517 =
                      let uu____66522 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66522  in
                    FStar_TypeChecker_NBETerm.embed uu____66517 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66516  in
                [uu____66511]  in
              uu____66495 :: uu____66504  in
            uu____66479 :: uu____66488  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66472
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____66550 =
            let uu____66557 =
              let uu____66562 =
                let uu____66563 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66563 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66562  in
            let uu____66566 =
              let uu____66573 =
                let uu____66578 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66578  in
              let uu____66579 =
                let uu____66586 =
                  let uu____66591 =
                    let uu____66592 =
                      let uu____66597 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66597  in
                    FStar_TypeChecker_NBETerm.embed uu____66592 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66591  in
                [uu____66586]  in
              uu____66573 :: uu____66579  in
            uu____66557 :: uu____66566  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66550
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66638,(b,uu____66640)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____66659 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66659
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66666  -> FStar_Pervasives_Native.Some _66666)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66668,(b,uu____66670)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____66689 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66689
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66696  -> FStar_Pervasives_Native.Some _66696)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66698,(f,uu____66700)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____66719 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____66719
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _66726  -> FStar_Pervasives_Native.Some _66726)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66728,(r,uu____66730)::(l,uu____66732)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____66755 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____66755
            (fun l1  ->
               let uu____66761 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____66761
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _66768  -> FStar_Pervasives_Native.Some _66768)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66770,(t1,uu____66772)::(b,uu____66774)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____66797 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66797
            (fun b1  ->
               let uu____66803 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66803
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66810  -> FStar_Pervasives_Native.Some _66810)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66812,(t1,uu____66814)::(b,uu____66816)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____66839 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66839
            (fun b1  ->
               let uu____66845 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____66845
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _66852  -> FStar_Pervasives_Native.Some _66852)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66854,(u,uu____66856)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____66875 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____66875
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _66882  -> FStar_Pervasives_Native.Some _66882)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66884,(t1,uu____66886)::(b,uu____66888)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____66911 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66911
            (fun b1  ->
               let uu____66917 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66917
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66924  -> FStar_Pervasives_Native.Some _66924)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66926,(c,uu____66928)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____66947 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____66947
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _66954  -> FStar_Pervasives_Native.Some _66954)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66956,(l,uu____66958)::(u,uu____66960)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____66983 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____66983
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _66992  -> FStar_Pervasives_Native.Some _66992)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66994,(t2,uu____66996)::(t1,uu____66998)::(b,uu____67000)::
           (r,uu____67002)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____67033 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____67033
            (fun r1  ->
               let uu____67043 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____67043
                 (fun b1  ->
                    let uu____67049 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____67049
                      (fun t11  ->
                         let uu____67055 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____67055
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _67062  ->
                                   FStar_Pervasives_Native.Some _67062)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67065,(brs,uu____67067)::(t1,uu____67069)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____67092 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____67092
            (fun t2  ->
               let uu____67098 =
                 let uu____67103 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____67103 cb brs  in
               FStar_Util.bind_opt uu____67098
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _67118  -> FStar_Pervasives_Native.Some _67118)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67122,(tacopt,uu____67124)::(t1,uu____67126)::(e,uu____67128)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____67155 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67155
            (fun e1  ->
               let uu____67161 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____67161
                 (fun t2  ->
                    let uu____67167 =
                      let uu____67172 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67172 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67167
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67187  ->
                              FStar_Pervasives_Native.Some _67187)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67191,(tacopt,uu____67193)::(c,uu____67195)::(e,uu____67197)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____67224 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67224
            (fun e1  ->
               let uu____67230 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____67230
                 (fun c1  ->
                    let uu____67236 =
                      let uu____67241 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67241 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67236
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67256  ->
                              FStar_Pervasives_Native.Some _67256)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____67260,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _67277  -> FStar_Pervasives_Native.Some _67277)
            FStar_Reflection_Data.Tv_Unknown
      | uu____67278 ->
          ((let uu____67280 =
              let uu____67286 =
                let uu____67288 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____67288
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____67286)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____67280);
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
    let uu____67315 =
      let uu____67322 =
        let uu____67327 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____67327  in
      let uu____67329 =
        let uu____67336 =
          let uu____67341 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____67341  in
        let uu____67342 =
          let uu____67349 =
            let uu____67354 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67354  in
          [uu____67349]  in
        uu____67336 :: uu____67342  in
      uu____67322 :: uu____67329  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____67315
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67387,(s,uu____67389)::(idx,uu____67391)::(nm,uu____67393)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____67420 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____67420
          (fun nm1  ->
             let uu____67430 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____67430
               (fun idx1  ->
                  let uu____67436 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____67436
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _67443  -> FStar_Pervasives_Native.Some _67443)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____67444 ->
        ((let uu____67446 =
            let uu____67452 =
              let uu____67454 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____67454
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67452)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67446);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____67478 =
          let uu____67485 =
            let uu____67490 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____67490  in
          let uu____67491 =
            let uu____67498 =
              let uu____67503 =
                let uu____67504 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____67504 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____67503  in
            [uu____67498]  in
          uu____67485 :: uu____67491  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____67478
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____67528 =
          let uu____67535 =
            let uu____67540 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67540  in
          let uu____67541 =
            let uu____67548 =
              let uu____67553 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____67553  in
            [uu____67548]  in
          uu____67535 :: uu____67541  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____67528
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67586,(md,uu____67588)::(t1,uu____67590)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____67613 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____67613
          (fun t2  ->
             let uu____67619 =
               let uu____67624 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____67624 cb md  in
             FStar_Util.bind_opt uu____67619
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _67639  -> FStar_Pervasives_Native.Some _67639)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67643,(post,uu____67645)::(pre,uu____67647)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____67670 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____67670
          (fun pre1  ->
             let uu____67676 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____67676
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _67683  -> FStar_Pervasives_Native.Some _67683)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67685,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _67702  -> FStar_Pervasives_Native.Some _67702)
          FStar_Reflection_Data.C_Unknown
    | uu____67703 ->
        ((let uu____67705 =
            let uu____67711 =
              let uu____67713 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____67713
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67711)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67705);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67759,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67775,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67791,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____67806 ->
        ((let uu____67808 =
            let uu____67814 =
              let uu____67816 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____67816  in
            (FStar_Errors.Warning_NotEmbedded, uu____67814)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67808);
         FStar_Pervasives_Native.None)
     in
  let uu____67820 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____67820 
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
           FStar_Syntax_Syntax.ltyp = uu____67851;
           FStar_Syntax_Syntax.rng = uu____67852;_},uu____67853)
        ->
        let uu____67872 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____67872
    | uu____67873 ->
        ((let uu____67875 =
            let uu____67881 =
              let uu____67883 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____67883  in
            (FStar_Errors.Warning_NotEmbedded, uu____67881)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67875);
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
    let uu____67912 =
      let uu____67918 = FStar_Ident.range_of_id i  in
      let uu____67919 = FStar_Ident.text_of_id i  in
      (uu____67918, uu____67919)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____67912  in
  let unembed_ident cb t =
    let uu____67942 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____67942 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____67966 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____67966
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
    let uu____67976 =
      let uu____67984 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____67986 =
        let uu____67989 = fv_as_emb_typ range_fv  in
        let uu____67990 =
          let uu____67993 = fv_as_emb_typ string_fv  in [uu____67993]  in
        uu____67989 :: uu____67990  in
      (uu____67984, uu____67986)  in
    FStar_Syntax_Syntax.ET_app uu____67976  in
  let uu____67997 =
    let uu____67998 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____67999 =
      let uu____68006 =
        let uu____68011 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____68011  in
      let uu____68016 =
        let uu____68023 =
          let uu____68028 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____68028  in
        [uu____68023]  in
      uu____68006 :: uu____68016  in
    mkFV uu____67998 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____67999
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____67997 et 
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
        let uu____68085 =
          let uu____68092 =
            let uu____68097 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____68097  in
          let uu____68099 =
            let uu____68106 =
              let uu____68111 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68111  in
            let uu____68112 =
              let uu____68119 =
                let uu____68124 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____68124  in
              let uu____68127 =
                let uu____68134 =
                  let uu____68139 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68139  in
                let uu____68140 =
                  let uu____68147 =
                    let uu____68152 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68152  in
                  [uu____68147]  in
                uu____68134 :: uu____68140  in
              uu____68119 :: uu____68127  in
            uu____68106 :: uu____68112  in
          uu____68092 :: uu____68099  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____68085
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____68179 =
          let uu____68186 =
            let uu____68191 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68191  in
          let uu____68195 =
            let uu____68202 =
              let uu____68207 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68207  in
            [uu____68202]  in
          uu____68186 :: uu____68195  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____68179
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____68237 =
          let uu____68244 =
            let uu____68249 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68249  in
          let uu____68253 =
            let uu____68260 =
              let uu____68265 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____68265  in
            let uu____68268 =
              let uu____68275 =
                let uu____68280 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____68280  in
              let uu____68281 =
                let uu____68288 =
                  let uu____68293 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68293  in
                let uu____68294 =
                  let uu____68301 =
                    let uu____68306 =
                      let uu____68307 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____68307 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68306  in
                  [uu____68301]  in
                uu____68288 :: uu____68294  in
              uu____68275 :: uu____68281  in
            uu____68260 :: uu____68268  in
          uu____68244 :: uu____68253  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____68237
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68367,(dcs,uu____68369)::(t1,uu____68371)::(bs,uu____68373)::
         (us,uu____68375)::(nm,uu____68377)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____68412 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____68412
          (fun nm1  ->
             let uu____68430 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____68430
               (fun us1  ->
                  let uu____68444 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____68444
                    (fun bs1  ->
                       let uu____68450 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____68450
                         (fun t2  ->
                            let uu____68456 =
                              let uu____68464 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____68464
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____68456
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _68494  ->
                                      FStar_Pervasives_Native.Some _68494)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68502,(t1,uu____68504)::(ty,uu____68506)::(univs1,uu____68508)::
         (fvar1,uu____68510)::(r,uu____68512)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____68547 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____68547
          (fun r1  ->
             let uu____68557 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____68557
               (fun fvar2  ->
                  let uu____68563 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____68563
                    (fun univs2  ->
                       let uu____68577 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____68577
                         (fun ty1  ->
                            let uu____68583 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____68583
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _68590  ->
                                      FStar_Pervasives_Native.Some _68590)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68595,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____68610 ->
        ((let uu____68612 =
            let uu____68618 =
              let uu____68620 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____68620
               in
            (FStar_Errors.Warning_NotEmbedded, uu____68618)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68612);
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
        let uu____68643 =
          let uu____68650 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____68650]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____68643
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____68665 =
          let uu____68672 =
            let uu____68677 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____68677  in
          let uu____68678 =
            let uu____68685 =
              let uu____68690 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____68690  in
            [uu____68685]  in
          uu____68672 :: uu____68678  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____68665
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68719,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68735,(i,uu____68737)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____68756 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____68756
          (fun i1  ->
             FStar_All.pipe_left
               (fun _68763  -> FStar_Pervasives_Native.Some _68763)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68765,(e2,uu____68767)::(e1,uu____68769)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____68792 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____68792
          (fun e11  ->
             let uu____68798 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____68798
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _68805  -> FStar_Pervasives_Native.Some _68805)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____68806 ->
        ((let uu____68808 =
            let uu____68814 =
              let uu____68816 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____68816  in
            (FStar_Errors.Warning_NotEmbedded, uu____68814)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68808);
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