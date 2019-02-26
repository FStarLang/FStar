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
    let uu____64236 =
      let uu____64244 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____64244, [])  in
    FStar_Syntax_Syntax.ET_app uu____64236
  
let mk_emb' :
  'Auu____64258 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____64258 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____64258 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____64258 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____64300 = mkFV fv [] []  in
        let uu____64305 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____64300 uu____64305
  
let mk_lazy :
  'Auu____64317 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____64317 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____64343 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____64343;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____64349  ->
                 let uu____64350 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____64350)
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
           FStar_Syntax_Syntax.ltyp = uu____64435;
           FStar_Syntax_Syntax.rng = uu____64436;_},uu____64437)
        ->
        let uu____64456 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64459  -> FStar_Pervasives_Native.Some _64459) uu____64456
    | uu____64460 ->
        ((let uu____64462 =
            let uu____64468 =
              let uu____64470 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____64470  in
            (FStar_Errors.Warning_NotEmbedded, uu____64468)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64462);
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
           FStar_Syntax_Syntax.ltyp = uu____64504;
           FStar_Syntax_Syntax.rng = uu____64505;_},uu____64506)
        ->
        let uu____64525 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64525
    | uu____64526 ->
        ((let uu____64528 =
            let uu____64534 =
              let uu____64536 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____64536  in
            (FStar_Errors.Warning_NotEmbedded, uu____64534)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64528);
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
          let uu____64586 = f x  in
          FStar_Util.bind_opt uu____64586
            (fun x1  ->
               let uu____64594 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64594
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
      | uu____64664 -> FStar_Pervasives_Native.None  in
    let uu____64665 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____64670 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____64665;
      FStar_TypeChecker_NBETerm.emb_typ = uu____64670
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
        let uu____64703 =
          let uu____64710 =
            let uu____64715 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____64715  in
          [uu____64710]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____64703
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____64767)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____64784 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____64784
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____64789 ->
        ((let uu____64791 =
            let uu____64797 =
              let uu____64799 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____64799  in
            (FStar_Errors.Warning_NotEmbedded, uu____64797)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64791);
         FStar_Pervasives_Native.None)
     in
  let uu____64803 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____64808 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____64803
    uu____64808
  
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
           FStar_Syntax_Syntax.ltyp = uu____64842;
           FStar_Syntax_Syntax.rng = uu____64843;_},uu____64844)
        ->
        let uu____64863 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64863
    | uu____64864 ->
        ((let uu____64866 =
            let uu____64872 =
              let uu____64874 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____64874  in
            (FStar_Errors.Warning_NotEmbedded, uu____64872)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64866);
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
           FStar_Syntax_Syntax.ltyp = uu____64908;
           FStar_Syntax_Syntax.rng = uu____64909;_},uu____64910)
        ->
        let uu____64929 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64929
    | uu____64930 ->
        ((let uu____64932 =
            let uu____64938 =
              let uu____64940 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____64940  in
            (FStar_Errors.Warning_NotEmbedded, uu____64938)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64932);
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
           FStar_Syntax_Syntax.ltyp = uu____64974;
           FStar_Syntax_Syntax.rng = uu____64975;_},uu____64976)
        ->
        let uu____64995 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64995
    | uu____64996 ->
        ((let uu____64998 =
            let uu____65004 =
              let uu____65006 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____65006  in
            (FStar_Errors.Warning_NotEmbedded, uu____65004)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64998);
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
        let uu____65037 =
          let uu____65044 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____65044]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____65037
    | FStar_Reflection_Data.C_String s ->
        let uu____65059 =
          let uu____65066 =
            let uu____65071 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65071  in
          [uu____65066]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____65059
    | FStar_Reflection_Data.C_Range r ->
        let uu____65082 =
          let uu____65089 =
            let uu____65094 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65094  in
          [uu____65089]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____65082
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____65108 =
          let uu____65115 =
            let uu____65120 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65120  in
          [uu____65115]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____65108
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____65188)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____65205 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____65205
          (fun i1  ->
             FStar_All.pipe_left
               (fun _65212  -> FStar_Pervasives_Native.Some _65212)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____65215)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____65232 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____65232
          (fun s1  ->
             FStar_All.pipe_left
               (fun _65243  -> FStar_Pervasives_Native.Some _65243)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____65246)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____65263 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____65263
          (fun r1  ->
             FStar_All.pipe_left
               (fun _65270  -> FStar_Pervasives_Native.Some _65270)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____65286)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____65303 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____65303
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _65322  -> FStar_Pervasives_Native.Some _65322)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____65323 ->
        ((let uu____65325 =
            let uu____65331 =
              let uu____65333 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____65333  in
            (FStar_Errors.Warning_NotEmbedded, uu____65331)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65325);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____65344  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65357 =
            let uu____65364 =
              let uu____65369 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65369  in
            [uu____65364]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____65357
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65384 =
            let uu____65391 =
              let uu____65396 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65396  in
            let uu____65397 =
              let uu____65404 =
                let uu____65409 =
                  let uu____65410 =
                    let uu____65415 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____65415  in
                  FStar_TypeChecker_NBETerm.embed uu____65410 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____65409  in
              [uu____65404]  in
            uu____65391 :: uu____65397  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____65384
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65433 =
            let uu____65440 =
              let uu____65445 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65445  in
            [uu____65440]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____65433
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65455 =
            let uu____65462 =
              let uu____65467 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65467  in
            [uu____65462]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____65455
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65478 =
            let uu____65485 =
              let uu____65490 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65490  in
            let uu____65491 =
              let uu____65498 =
                let uu____65503 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____65503  in
              [uu____65498]  in
            uu____65485 :: uu____65491  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____65478
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____65533)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____65550 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____65550
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _65557  -> FStar_Pervasives_Native.Some _65557)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____65560)::(f,uu____65562)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____65583 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____65583
            (fun f1  ->
               let uu____65589 =
                 let uu____65594 =
                   let uu____65599 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____65599  in
                 FStar_TypeChecker_NBETerm.unembed uu____65594 cb ps  in
               FStar_Util.bind_opt uu____65589
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _65612  -> FStar_Pervasives_Native.Some _65612)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65617)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____65634 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65634
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65641  -> FStar_Pervasives_Native.Some _65641)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65644)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____65661 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65661
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65668  -> FStar_Pervasives_Native.Some _65668)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____65671)::(bv,uu____65673)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____65694 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65694
            (fun bv1  ->
               let uu____65700 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____65700
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _65707  -> FStar_Pervasives_Native.Some _65707)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____65708 ->
          ((let uu____65710 =
              let uu____65716 =
                let uu____65718 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____65718
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65716)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____65710);
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
    let uu____65759 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____65759
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____65790 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____65790 e_aqualv
  
let rec unlazy_as_t :
  'Auu____65800 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____65800
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____65813;
             FStar_Syntax_Syntax.rng = uu____65814;_},uu____65815)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____65834 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____65872 =
            let uu____65879 =
              let uu____65884 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65884  in
            [uu____65879]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____65872
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____65894 =
            let uu____65901 =
              let uu____65906 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65906  in
            [uu____65901]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____65894
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____65916 =
            let uu____65923 =
              let uu____65928 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65928  in
            [uu____65923]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____65916
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____65939 =
            let uu____65946 =
              let uu____65951 =
                let uu____65952 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____65952 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____65951  in
            let uu____65955 =
              let uu____65962 =
                let uu____65967 =
                  let uu____65968 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____65968 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____65967  in
              [uu____65962]  in
            uu____65946 :: uu____65955  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____65939
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____65993 =
            let uu____66000 =
              let uu____66005 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66005  in
            let uu____66006 =
              let uu____66013 =
                let uu____66018 =
                  let uu____66019 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66019 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66018  in
              [uu____66013]  in
            uu____66000 :: uu____66006  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____65993
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66036 =
            let uu____66043 =
              let uu____66048 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66048  in
            let uu____66049 =
              let uu____66056 =
                let uu____66061 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66061  in
              [uu____66056]  in
            uu____66043 :: uu____66049  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____66036
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66075 =
            let uu____66082 =
              let uu____66087 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66087  in
            [uu____66082]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____66075
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____66098 =
            let uu____66105 =
              let uu____66110 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66110  in
            let uu____66111 =
              let uu____66118 =
                let uu____66123 =
                  let uu____66124 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66124 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66123  in
              [uu____66118]  in
            uu____66105 :: uu____66111  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____66098
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66140 =
            let uu____66147 =
              let uu____66152 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66152  in
            [uu____66147]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____66140
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66163 =
            let uu____66170 =
              let uu____66175 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66175  in
            let uu____66176 =
              let uu____66183 =
                let uu____66188 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66188  in
              [uu____66183]  in
            uu____66170 :: uu____66176  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____66163
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66211 =
            let uu____66218 =
              let uu____66223 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66223  in
            let uu____66225 =
              let uu____66232 =
                let uu____66237 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66237  in
              let uu____66238 =
                let uu____66245 =
                  let uu____66250 =
                    let uu____66251 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____66251 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66250  in
                let uu____66254 =
                  let uu____66261 =
                    let uu____66266 =
                      let uu____66267 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____66267 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____66266  in
                  [uu____66261]  in
                uu____66245 :: uu____66254  in
              uu____66232 :: uu____66238  in
            uu____66218 :: uu____66225  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____66211
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____66296 =
            let uu____66303 =
              let uu____66308 =
                let uu____66309 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66309 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____66308  in
            let uu____66312 =
              let uu____66319 =
                let uu____66324 =
                  let uu____66325 =
                    let uu____66334 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____66334  in
                  FStar_TypeChecker_NBETerm.embed uu____66325 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____66324  in
              [uu____66319]  in
            uu____66303 :: uu____66312  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____66296
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____66370 =
            let uu____66377 =
              let uu____66382 =
                let uu____66383 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66383 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66382  in
            let uu____66386 =
              let uu____66393 =
                let uu____66398 =
                  let uu____66399 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66399 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66398  in
              let uu____66402 =
                let uu____66409 =
                  let uu____66414 =
                    let uu____66415 =
                      let uu____66420 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66420  in
                    FStar_TypeChecker_NBETerm.embed uu____66415 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66414  in
                [uu____66409]  in
              uu____66393 :: uu____66402  in
            uu____66377 :: uu____66386  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66370
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____66448 =
            let uu____66455 =
              let uu____66460 =
                let uu____66461 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66461 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66460  in
            let uu____66464 =
              let uu____66471 =
                let uu____66476 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66476  in
              let uu____66477 =
                let uu____66484 =
                  let uu____66489 =
                    let uu____66490 =
                      let uu____66495 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66495  in
                    FStar_TypeChecker_NBETerm.embed uu____66490 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66489  in
                [uu____66484]  in
              uu____66471 :: uu____66477  in
            uu____66455 :: uu____66464  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66448
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66536,(b,uu____66538)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____66557 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66557
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66564  -> FStar_Pervasives_Native.Some _66564)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66566,(b,uu____66568)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____66587 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66587
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66594  -> FStar_Pervasives_Native.Some _66594)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66596,(f,uu____66598)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____66617 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____66617
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _66624  -> FStar_Pervasives_Native.Some _66624)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66626,(r,uu____66628)::(l,uu____66630)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____66653 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____66653
            (fun l1  ->
               let uu____66659 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____66659
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _66666  -> FStar_Pervasives_Native.Some _66666)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66668,(t1,uu____66670)::(b,uu____66672)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____66695 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66695
            (fun b1  ->
               let uu____66701 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66701
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66708  -> FStar_Pervasives_Native.Some _66708)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66710,(t1,uu____66712)::(b,uu____66714)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____66737 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66737
            (fun b1  ->
               let uu____66743 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____66743
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _66750  -> FStar_Pervasives_Native.Some _66750)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66752,(u,uu____66754)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____66773 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____66773
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _66780  -> FStar_Pervasives_Native.Some _66780)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66782,(t1,uu____66784)::(b,uu____66786)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____66809 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66809
            (fun b1  ->
               let uu____66815 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66815
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66822  -> FStar_Pervasives_Native.Some _66822)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66824,(c,uu____66826)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____66845 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____66845
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _66852  -> FStar_Pervasives_Native.Some _66852)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66854,(l,uu____66856)::(u,uu____66858)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____66881 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____66881
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _66890  -> FStar_Pervasives_Native.Some _66890)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66892,(t2,uu____66894)::(t1,uu____66896)::(b,uu____66898)::
           (r,uu____66900)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____66931 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____66931
            (fun r1  ->
               let uu____66941 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____66941
                 (fun b1  ->
                    let uu____66947 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____66947
                      (fun t11  ->
                         let uu____66953 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____66953
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _66960  ->
                                   FStar_Pervasives_Native.Some _66960)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66963,(brs,uu____66965)::(t1,uu____66967)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____66990 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____66990
            (fun t2  ->
               let uu____66996 =
                 let uu____67001 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____67001 cb brs  in
               FStar_Util.bind_opt uu____66996
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _67016  -> FStar_Pervasives_Native.Some _67016)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67020,(tacopt,uu____67022)::(t1,uu____67024)::(e,uu____67026)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____67053 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67053
            (fun e1  ->
               let uu____67059 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____67059
                 (fun t2  ->
                    let uu____67065 =
                      let uu____67070 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67070 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67065
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67085  ->
                              FStar_Pervasives_Native.Some _67085)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67089,(tacopt,uu____67091)::(c,uu____67093)::(e,uu____67095)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____67122 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67122
            (fun e1  ->
               let uu____67128 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____67128
                 (fun c1  ->
                    let uu____67134 =
                      let uu____67139 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67139 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67134
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67154  ->
                              FStar_Pervasives_Native.Some _67154)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____67158,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _67175  -> FStar_Pervasives_Native.Some _67175)
            FStar_Reflection_Data.Tv_Unknown
      | uu____67176 ->
          ((let uu____67178 =
              let uu____67184 =
                let uu____67186 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____67186
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____67184)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____67178);
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
    let uu____67213 =
      let uu____67220 =
        let uu____67225 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____67225  in
      let uu____67227 =
        let uu____67234 =
          let uu____67239 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____67239  in
        let uu____67240 =
          let uu____67247 =
            let uu____67252 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67252  in
          [uu____67247]  in
        uu____67234 :: uu____67240  in
      uu____67220 :: uu____67227  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____67213
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67285,(s,uu____67287)::(idx,uu____67289)::(nm,uu____67291)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____67318 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____67318
          (fun nm1  ->
             let uu____67328 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____67328
               (fun idx1  ->
                  let uu____67334 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____67334
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _67341  -> FStar_Pervasives_Native.Some _67341)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____67342 ->
        ((let uu____67344 =
            let uu____67350 =
              let uu____67352 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____67352
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67350)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67344);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____67376 =
          let uu____67383 =
            let uu____67388 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____67388  in
          let uu____67389 =
            let uu____67396 =
              let uu____67401 =
                let uu____67402 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____67402 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____67401  in
            [uu____67396]  in
          uu____67383 :: uu____67389  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____67376
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____67426 =
          let uu____67433 =
            let uu____67438 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67438  in
          let uu____67439 =
            let uu____67446 =
              let uu____67451 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____67451  in
            [uu____67446]  in
          uu____67433 :: uu____67439  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____67426
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67484,(md,uu____67486)::(t1,uu____67488)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____67511 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____67511
          (fun t2  ->
             let uu____67517 =
               let uu____67522 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____67522 cb md  in
             FStar_Util.bind_opt uu____67517
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _67537  -> FStar_Pervasives_Native.Some _67537)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67541,(post,uu____67543)::(pre,uu____67545)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____67568 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____67568
          (fun pre1  ->
             let uu____67574 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____67574
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _67581  -> FStar_Pervasives_Native.Some _67581)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67583,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _67600  -> FStar_Pervasives_Native.Some _67600)
          FStar_Reflection_Data.C_Unknown
    | uu____67601 ->
        ((let uu____67603 =
            let uu____67609 =
              let uu____67611 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____67611
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67609)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67603);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67657,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67673,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67689,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____67704 ->
        ((let uu____67706 =
            let uu____67712 =
              let uu____67714 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____67714  in
            (FStar_Errors.Warning_NotEmbedded, uu____67712)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67706);
         FStar_Pervasives_Native.None)
     in
  let uu____67718 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____67718 
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
           FStar_Syntax_Syntax.ltyp = uu____67749;
           FStar_Syntax_Syntax.rng = uu____67750;_},uu____67751)
        ->
        let uu____67770 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____67770
    | uu____67771 ->
        ((let uu____67773 =
            let uu____67779 =
              let uu____67781 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____67781  in
            (FStar_Errors.Warning_NotEmbedded, uu____67779)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67773);
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
    let uu____67810 =
      let uu____67816 = FStar_Ident.range_of_id i  in
      let uu____67817 = FStar_Ident.text_of_id i  in
      (uu____67816, uu____67817)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____67810  in
  let unembed_ident cb t =
    let uu____67840 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____67840 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____67864 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____67864
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
    let uu____67874 =
      let uu____67882 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____67884 =
        let uu____67887 = fv_as_emb_typ range_fv  in
        let uu____67888 =
          let uu____67891 = fv_as_emb_typ string_fv  in [uu____67891]  in
        uu____67887 :: uu____67888  in
      (uu____67882, uu____67884)  in
    FStar_Syntax_Syntax.ET_app uu____67874  in
  let uu____67895 =
    let uu____67896 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____67897 =
      let uu____67904 =
        let uu____67909 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____67909  in
      let uu____67914 =
        let uu____67921 =
          let uu____67926 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____67926  in
        [uu____67921]  in
      uu____67904 :: uu____67914  in
    mkFV uu____67896 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____67897
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____67895 et 
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
        let uu____67983 =
          let uu____67990 =
            let uu____67995 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67995  in
          let uu____67997 =
            let uu____68004 =
              let uu____68009 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68009  in
            let uu____68010 =
              let uu____68017 =
                let uu____68022 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____68022  in
              let uu____68025 =
                let uu____68032 =
                  let uu____68037 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68037  in
                let uu____68038 =
                  let uu____68045 =
                    let uu____68050 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68050  in
                  [uu____68045]  in
                uu____68032 :: uu____68038  in
              uu____68017 :: uu____68025  in
            uu____68004 :: uu____68010  in
          uu____67990 :: uu____67997  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____67983
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____68077 =
          let uu____68084 =
            let uu____68089 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68089  in
          let uu____68093 =
            let uu____68100 =
              let uu____68105 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68105  in
            [uu____68100]  in
          uu____68084 :: uu____68093  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____68077
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____68135 =
          let uu____68142 =
            let uu____68147 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68147  in
          let uu____68151 =
            let uu____68158 =
              let uu____68163 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____68163  in
            let uu____68166 =
              let uu____68173 =
                let uu____68178 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____68178  in
              let uu____68179 =
                let uu____68186 =
                  let uu____68191 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68191  in
                let uu____68192 =
                  let uu____68199 =
                    let uu____68204 =
                      let uu____68205 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____68205 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68204  in
                  [uu____68199]  in
                uu____68186 :: uu____68192  in
              uu____68173 :: uu____68179  in
            uu____68158 :: uu____68166  in
          uu____68142 :: uu____68151  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____68135
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68265,(dcs,uu____68267)::(t1,uu____68269)::(bs,uu____68271)::
         (us,uu____68273)::(nm,uu____68275)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____68310 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____68310
          (fun nm1  ->
             let uu____68328 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____68328
               (fun us1  ->
                  let uu____68342 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____68342
                    (fun bs1  ->
                       let uu____68348 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____68348
                         (fun t2  ->
                            let uu____68354 =
                              let uu____68362 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____68362
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____68354
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _68392  ->
                                      FStar_Pervasives_Native.Some _68392)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68400,(t1,uu____68402)::(ty,uu____68404)::(univs1,uu____68406)::
         (fvar1,uu____68408)::(r,uu____68410)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____68445 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____68445
          (fun r1  ->
             let uu____68455 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____68455
               (fun fvar2  ->
                  let uu____68461 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____68461
                    (fun univs2  ->
                       let uu____68475 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____68475
                         (fun ty1  ->
                            let uu____68481 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____68481
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _68488  ->
                                      FStar_Pervasives_Native.Some _68488)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68493,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____68508 ->
        ((let uu____68510 =
            let uu____68516 =
              let uu____68518 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____68518
               in
            (FStar_Errors.Warning_NotEmbedded, uu____68516)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68510);
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
        let uu____68541 =
          let uu____68548 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____68548]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____68541
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____68563 =
          let uu____68570 =
            let uu____68575 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____68575  in
          let uu____68576 =
            let uu____68583 =
              let uu____68588 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____68588  in
            [uu____68583]  in
          uu____68570 :: uu____68576  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____68563
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68617,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68633,(i,uu____68635)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____68654 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____68654
          (fun i1  ->
             FStar_All.pipe_left
               (fun _68661  -> FStar_Pervasives_Native.Some _68661)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68663,(e2,uu____68665)::(e1,uu____68667)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____68690 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____68690
          (fun e11  ->
             let uu____68696 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____68696
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _68703  -> FStar_Pervasives_Native.Some _68703)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____68704 ->
        ((let uu____68706 =
            let uu____68712 =
              let uu____68714 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____68714  in
            (FStar_Errors.Warning_NotEmbedded, uu____68712)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68706);
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