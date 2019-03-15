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
    let uu____59423 =
      let uu____59431 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____59431, [])  in
    FStar_Syntax_Syntax.ET_app uu____59423
  
let mk_emb' :
  'Auu____59445 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____59445 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____59445 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____59445 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____59487 = mkFV fv [] []  in
        let uu____59492 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____59487 uu____59492
  
let mk_lazy :
  'Auu____59504 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____59504 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____59530 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____59530;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____59536  ->
                 let uu____59537 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____59537)
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
           FStar_Syntax_Syntax.ltyp = uu____59582;
           FStar_Syntax_Syntax.rng = uu____59583;_},uu____59584)
        ->
        let uu____59603 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _59606  -> FStar_Pervasives_Native.Some _59606) uu____59603
    | uu____59607 ->
        ((let uu____59609 =
            let uu____59615 =
              let uu____59617 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____59617  in
            (FStar_Errors.Warning_NotEmbedded, uu____59615)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59609);
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
           FStar_Syntax_Syntax.ltyp = uu____59651;
           FStar_Syntax_Syntax.rng = uu____59652;_},uu____59653)
        ->
        let uu____59672 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59672
    | uu____59673 ->
        ((let uu____59675 =
            let uu____59681 =
              let uu____59683 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____59683  in
            (FStar_Errors.Warning_NotEmbedded, uu____59681)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59675);
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
          let uu____59733 = f x  in
          FStar_Util.bind_opt uu____59733
            (fun x1  ->
               let uu____59741 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59741
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
      | uu____59811 -> FStar_Pervasives_Native.None  in
    let uu____59812 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____59817 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____59812;
      FStar_TypeChecker_NBETerm.emb_typ = uu____59817
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
        let uu____59850 =
          let uu____59857 =
            let uu____59862 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____59862  in
          [uu____59857]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____59850
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____59914)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____59931 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____59931
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____59936 ->
        ((let uu____59938 =
            let uu____59944 =
              let uu____59946 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____59946  in
            (FStar_Errors.Warning_NotEmbedded, uu____59944)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59938);
         FStar_Pervasives_Native.None)
     in
  let uu____59950 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____59955 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____59950
    uu____59955
  
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
           FStar_Syntax_Syntax.ltyp = uu____59989;
           FStar_Syntax_Syntax.rng = uu____59990;_},uu____59991)
        ->
        let uu____60010 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60010
    | uu____60011 ->
        ((let uu____60013 =
            let uu____60019 =
              let uu____60021 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____60021  in
            (FStar_Errors.Warning_NotEmbedded, uu____60019)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60013);
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
           FStar_Syntax_Syntax.ltyp = uu____60055;
           FStar_Syntax_Syntax.rng = uu____60056;_},uu____60057)
        ->
        let uu____60076 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60076
    | uu____60077 ->
        ((let uu____60079 =
            let uu____60085 =
              let uu____60087 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____60087  in
            (FStar_Errors.Warning_NotEmbedded, uu____60085)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60079);
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
           FStar_Syntax_Syntax.ltyp = uu____60121;
           FStar_Syntax_Syntax.rng = uu____60122;_},uu____60123)
        ->
        let uu____60142 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60142
    | uu____60143 ->
        ((let uu____60145 =
            let uu____60151 =
              let uu____60153 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____60153  in
            (FStar_Errors.Warning_NotEmbedded, uu____60151)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60145);
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
        let uu____60184 =
          let uu____60191 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____60191]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____60184
    | FStar_Reflection_Data.C_String s ->
        let uu____60206 =
          let uu____60213 =
            let uu____60218 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60218  in
          [uu____60213]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____60206
    | FStar_Reflection_Data.C_Range r ->
        let uu____60229 =
          let uu____60236 =
            let uu____60241 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60241  in
          [uu____60236]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____60229
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____60255 =
          let uu____60262 =
            let uu____60267 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60267  in
          [uu____60262]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____60255
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____60335)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____60352 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____60352
          (fun i1  ->
             FStar_All.pipe_left
               (fun _60359  -> FStar_Pervasives_Native.Some _60359)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____60362)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____60379 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____60379
          (fun s1  ->
             FStar_All.pipe_left
               (fun _60390  -> FStar_Pervasives_Native.Some _60390)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____60393)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____60410 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____60410
          (fun r1  ->
             FStar_All.pipe_left
               (fun _60417  -> FStar_Pervasives_Native.Some _60417)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____60433)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____60450 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____60450
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _60469  -> FStar_Pervasives_Native.Some _60469)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____60470 ->
        ((let uu____60472 =
            let uu____60478 =
              let uu____60480 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____60480  in
            (FStar_Errors.Warning_NotEmbedded, uu____60478)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60472);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____60491  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60504 =
            let uu____60511 =
              let uu____60516 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60516  in
            [uu____60511]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____60504
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60531 =
            let uu____60538 =
              let uu____60543 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60543  in
            let uu____60544 =
              let uu____60551 =
                let uu____60556 =
                  let uu____60557 =
                    let uu____60562 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____60562  in
                  FStar_TypeChecker_NBETerm.embed uu____60557 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____60556  in
              [uu____60551]  in
            uu____60538 :: uu____60544  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____60531
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60580 =
            let uu____60587 =
              let uu____60592 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60592  in
            [uu____60587]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____60580
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____60602 =
            let uu____60609 =
              let uu____60614 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60614  in
            [uu____60609]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____60602
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____60625 =
            let uu____60632 =
              let uu____60637 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60637  in
            let uu____60638 =
              let uu____60645 =
                let uu____60650 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____60650  in
              [uu____60645]  in
            uu____60632 :: uu____60638  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____60625
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____60680)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____60697 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____60697
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _60704  -> FStar_Pervasives_Native.Some _60704)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____60707)::(f,uu____60709)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____60730 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____60730
            (fun f1  ->
               let uu____60736 =
                 let uu____60741 =
                   let uu____60746 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____60746  in
                 FStar_TypeChecker_NBETerm.unembed uu____60741 cb ps  in
               FStar_Util.bind_opt uu____60736
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _60759  -> FStar_Pervasives_Native.Some _60759)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60764)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____60781 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60781
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60788  -> FStar_Pervasives_Native.Some _60788)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60791)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____60808 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60808
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60815  -> FStar_Pervasives_Native.Some _60815)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____60818)::(bv,uu____60820)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____60841 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60841
            (fun bv1  ->
               let uu____60847 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____60847
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _60854  -> FStar_Pervasives_Native.Some _60854)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____60855 ->
          ((let uu____60857 =
              let uu____60863 =
                let uu____60865 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____60865
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____60863)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____60857);
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
    let uu____60906 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____60906
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____60937 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____60937 e_aqualv
  
let rec unlazy_as_t :
  'Auu____60947 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____60947
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____60960;
             FStar_Syntax_Syntax.rng = uu____60961;_},uu____60962)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____60981 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61019 =
            let uu____61026 =
              let uu____61031 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61031  in
            [uu____61026]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____61019
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____61041 =
            let uu____61048 =
              let uu____61053 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61053  in
            [uu____61048]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____61041
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61063 =
            let uu____61070 =
              let uu____61075 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61075  in
            [uu____61070]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____61063
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61086 =
            let uu____61093 =
              let uu____61098 =
                let uu____61099 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61099 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____61098  in
            let uu____61102 =
              let uu____61109 =
                let uu____61114 =
                  let uu____61115 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61115 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____61114  in
              [uu____61109]  in
            uu____61093 :: uu____61102  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____61086
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____61140 =
            let uu____61147 =
              let uu____61152 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61152  in
            let uu____61153 =
              let uu____61160 =
                let uu____61165 =
                  let uu____61166 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61166 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61165  in
              [uu____61160]  in
            uu____61147 :: uu____61153  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____61140
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61183 =
            let uu____61190 =
              let uu____61195 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61195  in
            let uu____61196 =
              let uu____61203 =
                let uu____61208 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61208  in
              [uu____61203]  in
            uu____61190 :: uu____61196  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____61183
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61222 =
            let uu____61229 =
              let uu____61234 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61234  in
            [uu____61229]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____61222
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____61245 =
            let uu____61252 =
              let uu____61257 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61257  in
            let uu____61258 =
              let uu____61265 =
                let uu____61270 =
                  let uu____61271 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61271 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61270  in
              [uu____61265]  in
            uu____61252 :: uu____61258  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____61245
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61287 =
            let uu____61294 =
              let uu____61299 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61299  in
            [uu____61294]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____61287
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61310 =
            let uu____61317 =
              let uu____61322 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61322  in
            let uu____61323 =
              let uu____61330 =
                let uu____61335 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61335  in
              [uu____61330]  in
            uu____61317 :: uu____61323  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____61310
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____61358 =
            let uu____61365 =
              let uu____61370 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61370  in
            let uu____61372 =
              let uu____61379 =
                let uu____61384 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61384  in
              let uu____61385 =
                let uu____61392 =
                  let uu____61397 =
                    let uu____61398 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____61398 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61397  in
                let uu____61401 =
                  let uu____61408 =
                    let uu____61413 =
                      let uu____61414 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____61414 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____61413  in
                  [uu____61408]  in
                uu____61392 :: uu____61401  in
              uu____61379 :: uu____61385  in
            uu____61365 :: uu____61372  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____61358
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____61443 =
            let uu____61450 =
              let uu____61455 =
                let uu____61456 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61456 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____61455  in
            let uu____61459 =
              let uu____61466 =
                let uu____61471 =
                  let uu____61472 =
                    let uu____61481 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____61481  in
                  FStar_TypeChecker_NBETerm.embed uu____61472 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____61471  in
              [uu____61466]  in
            uu____61450 :: uu____61459  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____61443
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____61517 =
            let uu____61524 =
              let uu____61529 =
                let uu____61530 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61530 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61529  in
            let uu____61533 =
              let uu____61540 =
                let uu____61545 =
                  let uu____61546 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61546 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61545  in
              let uu____61549 =
                let uu____61556 =
                  let uu____61561 =
                    let uu____61562 =
                      let uu____61567 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61567  in
                    FStar_TypeChecker_NBETerm.embed uu____61562 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61561  in
                [uu____61556]  in
              uu____61540 :: uu____61549  in
            uu____61524 :: uu____61533  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61517
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____61595 =
            let uu____61602 =
              let uu____61607 =
                let uu____61608 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61608 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61607  in
            let uu____61611 =
              let uu____61618 =
                let uu____61623 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61623  in
              let uu____61624 =
                let uu____61631 =
                  let uu____61636 =
                    let uu____61637 =
                      let uu____61642 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61642  in
                    FStar_TypeChecker_NBETerm.embed uu____61637 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61636  in
                [uu____61631]  in
              uu____61618 :: uu____61624  in
            uu____61602 :: uu____61611  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61595
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61683,(b,uu____61685)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____61704 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61704
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61711  -> FStar_Pervasives_Native.Some _61711)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61713,(b,uu____61715)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____61734 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61734
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61741  -> FStar_Pervasives_Native.Some _61741)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61743,(f,uu____61745)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____61764 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____61764
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _61771  -> FStar_Pervasives_Native.Some _61771)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61773,(r,uu____61775)::(l,uu____61777)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____61800 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____61800
            (fun l1  ->
               let uu____61806 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____61806
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _61813  -> FStar_Pervasives_Native.Some _61813)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61815,(t1,uu____61817)::(b,uu____61819)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____61842 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61842
            (fun b1  ->
               let uu____61848 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61848
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _61855  -> FStar_Pervasives_Native.Some _61855)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61857,(t1,uu____61859)::(b,uu____61861)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____61884 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61884
            (fun b1  ->
               let uu____61890 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____61890
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _61897  -> FStar_Pervasives_Native.Some _61897)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61899,(u,uu____61901)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____61920 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____61920
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _61927  -> FStar_Pervasives_Native.Some _61927)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61929,(t1,uu____61931)::(b,uu____61933)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____61956 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61956
            (fun b1  ->
               let uu____61962 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61962
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _61969  -> FStar_Pervasives_Native.Some _61969)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61971,(c,uu____61973)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____61992 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____61992
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _61999  -> FStar_Pervasives_Native.Some _61999)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62001,(l,uu____62003)::(u,uu____62005)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____62028 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____62028
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _62037  -> FStar_Pervasives_Native.Some _62037)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62039,(t2,uu____62041)::(t1,uu____62043)::(b,uu____62045)::
           (r,uu____62047)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____62078 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____62078
            (fun r1  ->
               let uu____62088 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____62088
                 (fun b1  ->
                    let uu____62094 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____62094
                      (fun t11  ->
                         let uu____62100 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____62100
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _62107  ->
                                   FStar_Pervasives_Native.Some _62107)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62110,(brs,uu____62112)::(t1,uu____62114)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____62137 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____62137
            (fun t2  ->
               let uu____62143 =
                 let uu____62148 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____62148 cb brs  in
               FStar_Util.bind_opt uu____62143
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _62163  -> FStar_Pervasives_Native.Some _62163)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62167,(tacopt,uu____62169)::(t1,uu____62171)::(e,uu____62173)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____62200 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62200
            (fun e1  ->
               let uu____62206 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____62206
                 (fun t2  ->
                    let uu____62212 =
                      let uu____62217 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62217 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62212
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62232  ->
                              FStar_Pervasives_Native.Some _62232)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62236,(tacopt,uu____62238)::(c,uu____62240)::(e,uu____62242)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____62269 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62269
            (fun e1  ->
               let uu____62275 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____62275
                 (fun c1  ->
                    let uu____62281 =
                      let uu____62286 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62286 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62281
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62301  ->
                              FStar_Pervasives_Native.Some _62301)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____62305,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _62322  -> FStar_Pervasives_Native.Some _62322)
            FStar_Reflection_Data.Tv_Unknown
      | uu____62323 ->
          ((let uu____62325 =
              let uu____62331 =
                let uu____62333 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____62333
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____62331)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____62325);
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
    let uu____62360 =
      let uu____62367 =
        let uu____62372 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____62372  in
      let uu____62374 =
        let uu____62381 =
          let uu____62386 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____62386  in
        let uu____62387 =
          let uu____62394 =
            let uu____62399 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62399  in
          [uu____62394]  in
        uu____62381 :: uu____62387  in
      uu____62367 :: uu____62374  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____62360
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62432,(s,uu____62434)::(idx,uu____62436)::(nm,uu____62438)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____62465 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____62465
          (fun nm1  ->
             let uu____62475 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____62475
               (fun idx1  ->
                  let uu____62481 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____62481
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _62488  -> FStar_Pervasives_Native.Some _62488)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____62489 ->
        ((let uu____62491 =
            let uu____62497 =
              let uu____62499 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____62499
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62497)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62491);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____62523 =
          let uu____62530 =
            let uu____62535 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____62535  in
          let uu____62536 =
            let uu____62543 =
              let uu____62548 =
                let uu____62549 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____62549 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____62548  in
            [uu____62543]  in
          uu____62530 :: uu____62536  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____62523
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____62573 =
          let uu____62580 =
            let uu____62585 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62585  in
          let uu____62586 =
            let uu____62593 =
              let uu____62598 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____62598  in
            [uu____62593]  in
          uu____62580 :: uu____62586  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____62573
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62631,(md,uu____62633)::(t1,uu____62635)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____62658 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____62658
          (fun t2  ->
             let uu____62664 =
               let uu____62669 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____62669 cb md  in
             FStar_Util.bind_opt uu____62664
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _62684  -> FStar_Pervasives_Native.Some _62684)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62688,(post,uu____62690)::(pre,uu____62692)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____62715 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____62715
          (fun pre1  ->
             let uu____62721 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____62721
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _62728  -> FStar_Pervasives_Native.Some _62728)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62730,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _62747  -> FStar_Pervasives_Native.Some _62747)
          FStar_Reflection_Data.C_Unknown
    | uu____62748 ->
        ((let uu____62750 =
            let uu____62756 =
              let uu____62758 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____62758
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62756)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62750);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62804,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62820,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62836,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____62851 ->
        ((let uu____62853 =
            let uu____62859 =
              let uu____62861 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____62861  in
            (FStar_Errors.Warning_NotEmbedded, uu____62859)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62853);
         FStar_Pervasives_Native.None)
     in
  let uu____62865 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____62865 
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
           FStar_Syntax_Syntax.ltyp = uu____62896;
           FStar_Syntax_Syntax.rng = uu____62897;_},uu____62898)
        ->
        let uu____62917 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____62917
    | uu____62918 ->
        ((let uu____62920 =
            let uu____62926 =
              let uu____62928 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____62928  in
            (FStar_Errors.Warning_NotEmbedded, uu____62926)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62920);
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
    let uu____62957 =
      let uu____62963 = FStar_Ident.range_of_id i  in
      let uu____62964 = FStar_Ident.text_of_id i  in
      (uu____62963, uu____62964)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____62957  in
  let unembed_ident cb t =
    let uu____62987 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____62987 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____63011 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____63011
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
    let uu____63021 =
      let uu____63029 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____63031 =
        let uu____63034 = fv_as_emb_typ range_fv  in
        let uu____63035 =
          let uu____63038 = fv_as_emb_typ string_fv  in [uu____63038]  in
        uu____63034 :: uu____63035  in
      (uu____63029, uu____63031)  in
    FStar_Syntax_Syntax.ET_app uu____63021  in
  let uu____63042 =
    let uu____63043 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____63044 =
      let uu____63051 =
        let uu____63056 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____63056  in
      let uu____63061 =
        let uu____63068 =
          let uu____63073 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____63073  in
        [uu____63068]  in
      uu____63051 :: uu____63061  in
    mkFV uu____63043 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____63044
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____63042 et 
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
        let uu____63130 =
          let uu____63137 =
            let uu____63142 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____63142  in
          let uu____63144 =
            let uu____63151 =
              let uu____63156 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63156  in
            let uu____63157 =
              let uu____63164 =
                let uu____63169 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____63169  in
              let uu____63172 =
                let uu____63179 =
                  let uu____63184 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63184  in
                let uu____63185 =
                  let uu____63192 =
                    let uu____63197 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63197  in
                  [uu____63192]  in
                uu____63179 :: uu____63185  in
              uu____63164 :: uu____63172  in
            uu____63151 :: uu____63157  in
          uu____63137 :: uu____63144  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____63130
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____63224 =
          let uu____63231 =
            let uu____63236 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63236  in
          let uu____63240 =
            let uu____63247 =
              let uu____63252 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63252  in
            [uu____63247]  in
          uu____63231 :: uu____63240  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____63224
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____63282 =
          let uu____63289 =
            let uu____63294 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63294  in
          let uu____63298 =
            let uu____63305 =
              let uu____63310 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____63310  in
            let uu____63313 =
              let uu____63320 =
                let uu____63325 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____63325  in
              let uu____63326 =
                let uu____63333 =
                  let uu____63338 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63338  in
                let uu____63339 =
                  let uu____63346 =
                    let uu____63351 =
                      let uu____63352 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____63352 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63351  in
                  [uu____63346]  in
                uu____63333 :: uu____63339  in
              uu____63320 :: uu____63326  in
            uu____63305 :: uu____63313  in
          uu____63289 :: uu____63298  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____63282
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63412,(dcs,uu____63414)::(t1,uu____63416)::(bs,uu____63418)::
         (us,uu____63420)::(nm,uu____63422)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____63457 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____63457
          (fun nm1  ->
             let uu____63475 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____63475
               (fun us1  ->
                  let uu____63489 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____63489
                    (fun bs1  ->
                       let uu____63495 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____63495
                         (fun t2  ->
                            let uu____63501 =
                              let uu____63509 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____63509
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____63501
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _63539  ->
                                      FStar_Pervasives_Native.Some _63539)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63547,(t1,uu____63549)::(ty,uu____63551)::(univs1,uu____63553)::
         (fvar1,uu____63555)::(r,uu____63557)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____63592 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____63592
          (fun r1  ->
             let uu____63602 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____63602
               (fun fvar2  ->
                  let uu____63608 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____63608
                    (fun univs2  ->
                       let uu____63622 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____63622
                         (fun ty1  ->
                            let uu____63628 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____63628
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _63635  ->
                                      FStar_Pervasives_Native.Some _63635)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63640,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____63655 ->
        ((let uu____63657 =
            let uu____63663 =
              let uu____63665 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____63665
               in
            (FStar_Errors.Warning_NotEmbedded, uu____63663)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63657);
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
        let uu____63688 =
          let uu____63695 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____63695]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____63688
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____63710 =
          let uu____63717 =
            let uu____63722 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____63722  in
          let uu____63723 =
            let uu____63730 =
              let uu____63735 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____63735  in
            [uu____63730]  in
          uu____63717 :: uu____63723  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____63710
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63764,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63780,(i,uu____63782)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____63801 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____63801
          (fun i1  ->
             FStar_All.pipe_left
               (fun _63808  -> FStar_Pervasives_Native.Some _63808)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63810,(e2,uu____63812)::(e1,uu____63814)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____63837 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____63837
          (fun e11  ->
             let uu____63843 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____63843
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _63850  -> FStar_Pervasives_Native.Some _63850)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____63851 ->
        ((let uu____63853 =
            let uu____63859 =
              let uu____63861 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____63861  in
            (FStar_Errors.Warning_NotEmbedded, uu____63859)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63853);
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