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
    let uu____64333 =
      let uu____64341 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____64341, [])  in
    FStar_Syntax_Syntax.ET_app uu____64333
  
let mk_emb' :
  'Auu____64355 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____64355 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____64355 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____64355 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____64397 = mkFV fv [] []  in
        let uu____64402 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____64397 uu____64402
  
let mk_lazy :
  'Auu____64414 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____64414 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____64440 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____64440;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____64446  ->
                 let uu____64447 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____64447)
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
           FStar_Syntax_Syntax.ltyp = uu____64532;
           FStar_Syntax_Syntax.rng = uu____64533;_},uu____64534)
        ->
        let uu____64553 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64556  -> FStar_Pervasives_Native.Some _64556) uu____64553
    | uu____64557 ->
        ((let uu____64559 =
            let uu____64565 =
              let uu____64567 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____64567  in
            (FStar_Errors.Warning_NotEmbedded, uu____64565)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64559);
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
           FStar_Syntax_Syntax.ltyp = uu____64601;
           FStar_Syntax_Syntax.rng = uu____64602;_},uu____64603)
        ->
        let uu____64622 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64622
    | uu____64623 ->
        ((let uu____64625 =
            let uu____64631 =
              let uu____64633 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____64633  in
            (FStar_Errors.Warning_NotEmbedded, uu____64631)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64625);
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
          let uu____64683 = f x  in
          FStar_Util.bind_opt uu____64683
            (fun x1  ->
               let uu____64691 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64691
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
      | uu____64761 -> FStar_Pervasives_Native.None  in
    let uu____64762 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____64767 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____64762;
      FStar_TypeChecker_NBETerm.emb_typ = uu____64767
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
        let uu____64800 =
          let uu____64807 =
            let uu____64812 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____64812  in
          [uu____64807]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____64800
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____64864)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____64881 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____64881
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____64886 ->
        ((let uu____64888 =
            let uu____64894 =
              let uu____64896 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____64896  in
            (FStar_Errors.Warning_NotEmbedded, uu____64894)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64888);
         FStar_Pervasives_Native.None)
     in
  let uu____64900 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____64905 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____64900
    uu____64905
  
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
           FStar_Syntax_Syntax.ltyp = uu____64939;
           FStar_Syntax_Syntax.rng = uu____64940;_},uu____64941)
        ->
        let uu____64960 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64960
    | uu____64961 ->
        ((let uu____64963 =
            let uu____64969 =
              let uu____64971 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____64971  in
            (FStar_Errors.Warning_NotEmbedded, uu____64969)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64963);
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
           FStar_Syntax_Syntax.ltyp = uu____65005;
           FStar_Syntax_Syntax.rng = uu____65006;_},uu____65007)
        ->
        let uu____65026 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65026
    | uu____65027 ->
        ((let uu____65029 =
            let uu____65035 =
              let uu____65037 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____65037  in
            (FStar_Errors.Warning_NotEmbedded, uu____65035)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65029);
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
           FStar_Syntax_Syntax.ltyp = uu____65071;
           FStar_Syntax_Syntax.rng = uu____65072;_},uu____65073)
        ->
        let uu____65092 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65092
    | uu____65093 ->
        ((let uu____65095 =
            let uu____65101 =
              let uu____65103 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____65103  in
            (FStar_Errors.Warning_NotEmbedded, uu____65101)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65095);
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
        let uu____65134 =
          let uu____65141 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____65141]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____65134
    | FStar_Reflection_Data.C_String s ->
        let uu____65156 =
          let uu____65163 =
            let uu____65168 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65168  in
          [uu____65163]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____65156
    | FStar_Reflection_Data.C_Range r ->
        let uu____65179 =
          let uu____65186 =
            let uu____65191 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65191  in
          [uu____65186]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____65179
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____65205 =
          let uu____65212 =
            let uu____65217 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65217  in
          [uu____65212]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____65205
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____65285)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____65302 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____65302
          (fun i1  ->
             FStar_All.pipe_left
               (fun _65309  -> FStar_Pervasives_Native.Some _65309)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____65312)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____65329 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____65329
          (fun s1  ->
             FStar_All.pipe_left
               (fun _65340  -> FStar_Pervasives_Native.Some _65340)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____65343)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____65360 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____65360
          (fun r1  ->
             FStar_All.pipe_left
               (fun _65367  -> FStar_Pervasives_Native.Some _65367)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____65383)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____65400 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____65400
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _65419  -> FStar_Pervasives_Native.Some _65419)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____65420 ->
        ((let uu____65422 =
            let uu____65428 =
              let uu____65430 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____65430  in
            (FStar_Errors.Warning_NotEmbedded, uu____65428)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65422);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____65441  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65454 =
            let uu____65461 =
              let uu____65466 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65466  in
            [uu____65461]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____65454
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65481 =
            let uu____65488 =
              let uu____65493 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65493  in
            let uu____65494 =
              let uu____65501 =
                let uu____65506 =
                  let uu____65507 =
                    let uu____65512 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____65512  in
                  FStar_TypeChecker_NBETerm.embed uu____65507 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____65506  in
              [uu____65501]  in
            uu____65488 :: uu____65494  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____65481
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65530 =
            let uu____65537 =
              let uu____65542 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65542  in
            [uu____65537]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____65530
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65552 =
            let uu____65559 =
              let uu____65564 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65564  in
            [uu____65559]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____65552
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65575 =
            let uu____65582 =
              let uu____65587 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65587  in
            let uu____65588 =
              let uu____65595 =
                let uu____65600 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____65600  in
              [uu____65595]  in
            uu____65582 :: uu____65588  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____65575
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____65630)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____65647 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____65647
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _65654  -> FStar_Pervasives_Native.Some _65654)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____65657)::(f,uu____65659)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____65680 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____65680
            (fun f1  ->
               let uu____65686 =
                 let uu____65691 =
                   let uu____65696 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____65696  in
                 FStar_TypeChecker_NBETerm.unembed uu____65691 cb ps  in
               FStar_Util.bind_opt uu____65686
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _65709  -> FStar_Pervasives_Native.Some _65709)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65714)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____65731 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65731
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65738  -> FStar_Pervasives_Native.Some _65738)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65741)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____65758 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65758
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65765  -> FStar_Pervasives_Native.Some _65765)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____65768)::(bv,uu____65770)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____65791 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65791
            (fun bv1  ->
               let uu____65797 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____65797
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _65804  -> FStar_Pervasives_Native.Some _65804)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____65805 ->
          ((let uu____65807 =
              let uu____65813 =
                let uu____65815 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____65815
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65813)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____65807);
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
    let uu____65856 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____65856
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____65887 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____65887 e_aqualv
  
let rec unlazy_as_t :
  'Auu____65897 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____65897
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____65910;
             FStar_Syntax_Syntax.rng = uu____65911;_},uu____65912)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____65931 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____65969 =
            let uu____65976 =
              let uu____65981 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65981  in
            [uu____65976]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____65969
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____65991 =
            let uu____65998 =
              let uu____66003 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66003  in
            [uu____65998]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____65991
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____66013 =
            let uu____66020 =
              let uu____66025 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66025  in
            [uu____66020]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____66013
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66036 =
            let uu____66043 =
              let uu____66048 =
                let uu____66049 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66049 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____66048  in
            let uu____66052 =
              let uu____66059 =
                let uu____66064 =
                  let uu____66065 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66065 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____66064  in
              [uu____66059]  in
            uu____66043 :: uu____66052  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____66036
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____66090 =
            let uu____66097 =
              let uu____66102 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66102  in
            let uu____66103 =
              let uu____66110 =
                let uu____66115 =
                  let uu____66116 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66116 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66115  in
              [uu____66110]  in
            uu____66097 :: uu____66103  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____66090
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66133 =
            let uu____66140 =
              let uu____66145 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66145  in
            let uu____66146 =
              let uu____66153 =
                let uu____66158 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66158  in
              [uu____66153]  in
            uu____66140 :: uu____66146  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____66133
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66172 =
            let uu____66179 =
              let uu____66184 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66184  in
            [uu____66179]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____66172
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____66195 =
            let uu____66202 =
              let uu____66207 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66207  in
            let uu____66208 =
              let uu____66215 =
                let uu____66220 =
                  let uu____66221 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66221 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66220  in
              [uu____66215]  in
            uu____66202 :: uu____66208  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____66195
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66237 =
            let uu____66244 =
              let uu____66249 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66249  in
            [uu____66244]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____66237
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66260 =
            let uu____66267 =
              let uu____66272 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66272  in
            let uu____66273 =
              let uu____66280 =
                let uu____66285 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66285  in
              [uu____66280]  in
            uu____66267 :: uu____66273  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____66260
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66308 =
            let uu____66315 =
              let uu____66320 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66320  in
            let uu____66322 =
              let uu____66329 =
                let uu____66334 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66334  in
              let uu____66335 =
                let uu____66342 =
                  let uu____66347 =
                    let uu____66348 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____66348 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66347  in
                let uu____66351 =
                  let uu____66358 =
                    let uu____66363 =
                      let uu____66364 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____66364 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____66363  in
                  [uu____66358]  in
                uu____66342 :: uu____66351  in
              uu____66329 :: uu____66335  in
            uu____66315 :: uu____66322  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____66308
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____66393 =
            let uu____66400 =
              let uu____66405 =
                let uu____66406 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66406 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____66405  in
            let uu____66409 =
              let uu____66416 =
                let uu____66421 =
                  let uu____66422 =
                    let uu____66431 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____66431  in
                  FStar_TypeChecker_NBETerm.embed uu____66422 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____66421  in
              [uu____66416]  in
            uu____66400 :: uu____66409  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____66393
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____66467 =
            let uu____66474 =
              let uu____66479 =
                let uu____66480 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66480 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66479  in
            let uu____66483 =
              let uu____66490 =
                let uu____66495 =
                  let uu____66496 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66496 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66495  in
              let uu____66499 =
                let uu____66506 =
                  let uu____66511 =
                    let uu____66512 =
                      let uu____66517 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66517  in
                    FStar_TypeChecker_NBETerm.embed uu____66512 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66511  in
                [uu____66506]  in
              uu____66490 :: uu____66499  in
            uu____66474 :: uu____66483  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66467
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____66545 =
            let uu____66552 =
              let uu____66557 =
                let uu____66558 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66558 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66557  in
            let uu____66561 =
              let uu____66568 =
                let uu____66573 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66573  in
              let uu____66574 =
                let uu____66581 =
                  let uu____66586 =
                    let uu____66587 =
                      let uu____66592 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66592  in
                    FStar_TypeChecker_NBETerm.embed uu____66587 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66586  in
                [uu____66581]  in
              uu____66568 :: uu____66574  in
            uu____66552 :: uu____66561  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66545
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66633,(b,uu____66635)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____66654 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66654
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66661  -> FStar_Pervasives_Native.Some _66661)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66663,(b,uu____66665)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____66684 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66684
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66691  -> FStar_Pervasives_Native.Some _66691)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66693,(f,uu____66695)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____66714 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____66714
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _66721  -> FStar_Pervasives_Native.Some _66721)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66723,(r,uu____66725)::(l,uu____66727)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____66750 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____66750
            (fun l1  ->
               let uu____66756 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____66756
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _66763  -> FStar_Pervasives_Native.Some _66763)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66765,(t1,uu____66767)::(b,uu____66769)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____66792 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66792
            (fun b1  ->
               let uu____66798 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66798
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66805  -> FStar_Pervasives_Native.Some _66805)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66807,(t1,uu____66809)::(b,uu____66811)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____66834 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66834
            (fun b1  ->
               let uu____66840 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____66840
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _66847  -> FStar_Pervasives_Native.Some _66847)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66849,(u,uu____66851)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____66870 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____66870
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _66877  -> FStar_Pervasives_Native.Some _66877)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66879,(t1,uu____66881)::(b,uu____66883)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____66906 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66906
            (fun b1  ->
               let uu____66912 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66912
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66919  -> FStar_Pervasives_Native.Some _66919)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66921,(c,uu____66923)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____66942 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____66942
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _66949  -> FStar_Pervasives_Native.Some _66949)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66951,(l,uu____66953)::(u,uu____66955)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____66978 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____66978
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _66987  -> FStar_Pervasives_Native.Some _66987)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66989,(t2,uu____66991)::(t1,uu____66993)::(b,uu____66995)::
           (r,uu____66997)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____67028 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____67028
            (fun r1  ->
               let uu____67038 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____67038
                 (fun b1  ->
                    let uu____67044 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____67044
                      (fun t11  ->
                         let uu____67050 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____67050
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _67057  ->
                                   FStar_Pervasives_Native.Some _67057)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67060,(brs,uu____67062)::(t1,uu____67064)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____67087 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____67087
            (fun t2  ->
               let uu____67093 =
                 let uu____67098 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____67098 cb brs  in
               FStar_Util.bind_opt uu____67093
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _67113  -> FStar_Pervasives_Native.Some _67113)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67117,(tacopt,uu____67119)::(t1,uu____67121)::(e,uu____67123)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____67150 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67150
            (fun e1  ->
               let uu____67156 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____67156
                 (fun t2  ->
                    let uu____67162 =
                      let uu____67167 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67167 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67162
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67182  ->
                              FStar_Pervasives_Native.Some _67182)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67186,(tacopt,uu____67188)::(c,uu____67190)::(e,uu____67192)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____67219 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67219
            (fun e1  ->
               let uu____67225 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____67225
                 (fun c1  ->
                    let uu____67231 =
                      let uu____67236 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67236 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67231
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67251  ->
                              FStar_Pervasives_Native.Some _67251)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____67255,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _67272  -> FStar_Pervasives_Native.Some _67272)
            FStar_Reflection_Data.Tv_Unknown
      | uu____67273 ->
          ((let uu____67275 =
              let uu____67281 =
                let uu____67283 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____67283
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____67281)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____67275);
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
    let uu____67310 =
      let uu____67317 =
        let uu____67322 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____67322  in
      let uu____67324 =
        let uu____67331 =
          let uu____67336 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____67336  in
        let uu____67337 =
          let uu____67344 =
            let uu____67349 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67349  in
          [uu____67344]  in
        uu____67331 :: uu____67337  in
      uu____67317 :: uu____67324  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____67310
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67382,(s,uu____67384)::(idx,uu____67386)::(nm,uu____67388)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____67415 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____67415
          (fun nm1  ->
             let uu____67425 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____67425
               (fun idx1  ->
                  let uu____67431 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____67431
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _67438  -> FStar_Pervasives_Native.Some _67438)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____67439 ->
        ((let uu____67441 =
            let uu____67447 =
              let uu____67449 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____67449
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67447)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67441);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____67473 =
          let uu____67480 =
            let uu____67485 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____67485  in
          let uu____67486 =
            let uu____67493 =
              let uu____67498 =
                let uu____67499 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____67499 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____67498  in
            [uu____67493]  in
          uu____67480 :: uu____67486  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____67473
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____67523 =
          let uu____67530 =
            let uu____67535 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67535  in
          let uu____67536 =
            let uu____67543 =
              let uu____67548 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____67548  in
            [uu____67543]  in
          uu____67530 :: uu____67536  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____67523
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67581,(md,uu____67583)::(t1,uu____67585)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____67608 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____67608
          (fun t2  ->
             let uu____67614 =
               let uu____67619 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____67619 cb md  in
             FStar_Util.bind_opt uu____67614
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _67634  -> FStar_Pervasives_Native.Some _67634)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67638,(post,uu____67640)::(pre,uu____67642)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____67665 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____67665
          (fun pre1  ->
             let uu____67671 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____67671
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _67678  -> FStar_Pervasives_Native.Some _67678)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67680,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _67697  -> FStar_Pervasives_Native.Some _67697)
          FStar_Reflection_Data.C_Unknown
    | uu____67698 ->
        ((let uu____67700 =
            let uu____67706 =
              let uu____67708 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____67708
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67706)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67700);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67754,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67770,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67786,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____67801 ->
        ((let uu____67803 =
            let uu____67809 =
              let uu____67811 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____67811  in
            (FStar_Errors.Warning_NotEmbedded, uu____67809)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67803);
         FStar_Pervasives_Native.None)
     in
  let uu____67815 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____67815 
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
           FStar_Syntax_Syntax.ltyp = uu____67846;
           FStar_Syntax_Syntax.rng = uu____67847;_},uu____67848)
        ->
        let uu____67867 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____67867
    | uu____67868 ->
        ((let uu____67870 =
            let uu____67876 =
              let uu____67878 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____67878  in
            (FStar_Errors.Warning_NotEmbedded, uu____67876)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67870);
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
    let uu____67907 =
      let uu____67913 = FStar_Ident.range_of_id i  in
      let uu____67914 = FStar_Ident.text_of_id i  in
      (uu____67913, uu____67914)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____67907  in
  let unembed_ident cb t =
    let uu____67937 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____67937 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____67961 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____67961
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
    let uu____67971 =
      let uu____67979 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____67981 =
        let uu____67984 = fv_as_emb_typ range_fv  in
        let uu____67985 =
          let uu____67988 = fv_as_emb_typ string_fv  in [uu____67988]  in
        uu____67984 :: uu____67985  in
      (uu____67979, uu____67981)  in
    FStar_Syntax_Syntax.ET_app uu____67971  in
  let uu____67992 =
    let uu____67993 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____67994 =
      let uu____68001 =
        let uu____68006 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____68006  in
      let uu____68011 =
        let uu____68018 =
          let uu____68023 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____68023  in
        [uu____68018]  in
      uu____68001 :: uu____68011  in
    mkFV uu____67993 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____67994
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____67992 et 
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
        let uu____68080 =
          let uu____68087 =
            let uu____68092 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____68092  in
          let uu____68094 =
            let uu____68101 =
              let uu____68106 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68106  in
            let uu____68107 =
              let uu____68114 =
                let uu____68119 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____68119  in
              let uu____68122 =
                let uu____68129 =
                  let uu____68134 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68134  in
                let uu____68135 =
                  let uu____68142 =
                    let uu____68147 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68147  in
                  [uu____68142]  in
                uu____68129 :: uu____68135  in
              uu____68114 :: uu____68122  in
            uu____68101 :: uu____68107  in
          uu____68087 :: uu____68094  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____68080
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____68174 =
          let uu____68181 =
            let uu____68186 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68186  in
          let uu____68190 =
            let uu____68197 =
              let uu____68202 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68202  in
            [uu____68197]  in
          uu____68181 :: uu____68190  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____68174
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____68232 =
          let uu____68239 =
            let uu____68244 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68244  in
          let uu____68248 =
            let uu____68255 =
              let uu____68260 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____68260  in
            let uu____68263 =
              let uu____68270 =
                let uu____68275 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____68275  in
              let uu____68276 =
                let uu____68283 =
                  let uu____68288 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68288  in
                let uu____68289 =
                  let uu____68296 =
                    let uu____68301 =
                      let uu____68302 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____68302 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68301  in
                  [uu____68296]  in
                uu____68283 :: uu____68289  in
              uu____68270 :: uu____68276  in
            uu____68255 :: uu____68263  in
          uu____68239 :: uu____68248  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____68232
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68362,(dcs,uu____68364)::(t1,uu____68366)::(bs,uu____68368)::
         (us,uu____68370)::(nm,uu____68372)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____68407 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____68407
          (fun nm1  ->
             let uu____68425 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____68425
               (fun us1  ->
                  let uu____68439 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____68439
                    (fun bs1  ->
                       let uu____68445 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____68445
                         (fun t2  ->
                            let uu____68451 =
                              let uu____68459 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____68459
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____68451
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _68489  ->
                                      FStar_Pervasives_Native.Some _68489)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68497,(t1,uu____68499)::(ty,uu____68501)::(univs1,uu____68503)::
         (fvar1,uu____68505)::(r,uu____68507)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____68542 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____68542
          (fun r1  ->
             let uu____68552 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____68552
               (fun fvar2  ->
                  let uu____68558 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____68558
                    (fun univs2  ->
                       let uu____68572 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____68572
                         (fun ty1  ->
                            let uu____68578 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____68578
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _68585  ->
                                      FStar_Pervasives_Native.Some _68585)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68590,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____68605 ->
        ((let uu____68607 =
            let uu____68613 =
              let uu____68615 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____68615
               in
            (FStar_Errors.Warning_NotEmbedded, uu____68613)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68607);
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
        let uu____68638 =
          let uu____68645 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____68645]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____68638
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____68660 =
          let uu____68667 =
            let uu____68672 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____68672  in
          let uu____68673 =
            let uu____68680 =
              let uu____68685 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____68685  in
            [uu____68680]  in
          uu____68667 :: uu____68673  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____68660
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68714,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68730,(i,uu____68732)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____68751 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____68751
          (fun i1  ->
             FStar_All.pipe_left
               (fun _68758  -> FStar_Pervasives_Native.Some _68758)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68760,(e2,uu____68762)::(e1,uu____68764)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____68787 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____68787
          (fun e11  ->
             let uu____68793 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____68793
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _68800  -> FStar_Pervasives_Native.Some _68800)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____68801 ->
        ((let uu____68803 =
            let uu____68809 =
              let uu____68811 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____68811  in
            (FStar_Errors.Warning_NotEmbedded, uu____68809)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68803);
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