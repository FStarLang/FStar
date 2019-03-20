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
    let uu____59436 =
      let uu____59444 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____59444, [])  in
    FStar_Syntax_Syntax.ET_app uu____59436
  
let mk_emb' :
  'Auu____59458 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____59458 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____59458 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____59458 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____59500 = mkFV fv [] []  in
        let uu____59505 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____59500 uu____59505
  
let mk_lazy :
  'Auu____59517 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____59517 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____59543 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____59543;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____59549  ->
                 let uu____59550 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____59550)
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
           FStar_Syntax_Syntax.ltyp = uu____59595;
           FStar_Syntax_Syntax.rng = uu____59596;_},uu____59597)
        ->
        let uu____59616 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _59619  -> FStar_Pervasives_Native.Some _59619) uu____59616
    | uu____59620 ->
        ((let uu____59622 =
            let uu____59628 =
              let uu____59630 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____59630  in
            (FStar_Errors.Warning_NotEmbedded, uu____59628)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59622);
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
           FStar_Syntax_Syntax.ltyp = uu____59664;
           FStar_Syntax_Syntax.rng = uu____59665;_},uu____59666)
        ->
        let uu____59685 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59685
    | uu____59686 ->
        ((let uu____59688 =
            let uu____59694 =
              let uu____59696 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____59696  in
            (FStar_Errors.Warning_NotEmbedded, uu____59694)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59688);
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
          let uu____59746 = f x  in
          FStar_Util.bind_opt uu____59746
            (fun x1  ->
               let uu____59754 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59754
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
      | uu____59824 -> FStar_Pervasives_Native.None  in
    let uu____59825 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____59830 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____59825;
      FStar_TypeChecker_NBETerm.emb_typ = uu____59830
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
        let uu____59863 =
          let uu____59870 =
            let uu____59875 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____59875  in
          [uu____59870]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____59863
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____59927)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____59944 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____59944
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____59949 ->
        ((let uu____59951 =
            let uu____59957 =
              let uu____59959 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____59959  in
            (FStar_Errors.Warning_NotEmbedded, uu____59957)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59951);
         FStar_Pervasives_Native.None)
     in
  let uu____59963 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____59968 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____59963
    uu____59968
  
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
           FStar_Syntax_Syntax.ltyp = uu____60002;
           FStar_Syntax_Syntax.rng = uu____60003;_},uu____60004)
        ->
        let uu____60023 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60023
    | uu____60024 ->
        ((let uu____60026 =
            let uu____60032 =
              let uu____60034 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____60034  in
            (FStar_Errors.Warning_NotEmbedded, uu____60032)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60026);
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
           FStar_Syntax_Syntax.ltyp = uu____60068;
           FStar_Syntax_Syntax.rng = uu____60069;_},uu____60070)
        ->
        let uu____60089 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60089
    | uu____60090 ->
        ((let uu____60092 =
            let uu____60098 =
              let uu____60100 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____60100  in
            (FStar_Errors.Warning_NotEmbedded, uu____60098)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60092);
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
           FStar_Syntax_Syntax.ltyp = uu____60134;
           FStar_Syntax_Syntax.rng = uu____60135;_},uu____60136)
        ->
        let uu____60155 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60155
    | uu____60156 ->
        ((let uu____60158 =
            let uu____60164 =
              let uu____60166 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____60166  in
            (FStar_Errors.Warning_NotEmbedded, uu____60164)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60158);
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
        let uu____60197 =
          let uu____60204 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____60204]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____60197
    | FStar_Reflection_Data.C_String s ->
        let uu____60219 =
          let uu____60226 =
            let uu____60231 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60231  in
          [uu____60226]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____60219
    | FStar_Reflection_Data.C_Range r ->
        let uu____60242 =
          let uu____60249 =
            let uu____60254 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60254  in
          [uu____60249]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____60242
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____60268 =
          let uu____60275 =
            let uu____60280 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60280  in
          [uu____60275]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____60268
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____60348)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____60365 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____60365
          (fun i1  ->
             FStar_All.pipe_left
               (fun _60372  -> FStar_Pervasives_Native.Some _60372)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____60375)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____60392 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____60392
          (fun s1  ->
             FStar_All.pipe_left
               (fun _60403  -> FStar_Pervasives_Native.Some _60403)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____60406)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____60423 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____60423
          (fun r1  ->
             FStar_All.pipe_left
               (fun _60430  -> FStar_Pervasives_Native.Some _60430)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____60446)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____60463 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____60463
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _60482  -> FStar_Pervasives_Native.Some _60482)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____60483 ->
        ((let uu____60485 =
            let uu____60491 =
              let uu____60493 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____60493  in
            (FStar_Errors.Warning_NotEmbedded, uu____60491)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60485);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____60504  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60517 =
            let uu____60524 =
              let uu____60529 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60529  in
            [uu____60524]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____60517
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60544 =
            let uu____60551 =
              let uu____60556 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60556  in
            let uu____60557 =
              let uu____60564 =
                let uu____60569 =
                  let uu____60570 =
                    let uu____60575 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____60575  in
                  FStar_TypeChecker_NBETerm.embed uu____60570 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____60569  in
              [uu____60564]  in
            uu____60551 :: uu____60557  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____60544
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60593 =
            let uu____60600 =
              let uu____60605 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60605  in
            [uu____60600]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____60593
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____60615 =
            let uu____60622 =
              let uu____60627 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60627  in
            [uu____60622]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____60615
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____60638 =
            let uu____60645 =
              let uu____60650 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60650  in
            let uu____60651 =
              let uu____60658 =
                let uu____60663 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____60663  in
              [uu____60658]  in
            uu____60645 :: uu____60651  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____60638
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____60693)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____60710 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____60710
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _60717  -> FStar_Pervasives_Native.Some _60717)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____60720)::(f,uu____60722)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____60743 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____60743
            (fun f1  ->
               let uu____60749 =
                 let uu____60754 =
                   let uu____60759 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____60759  in
                 FStar_TypeChecker_NBETerm.unembed uu____60754 cb ps  in
               FStar_Util.bind_opt uu____60749
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _60772  -> FStar_Pervasives_Native.Some _60772)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60777)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____60794 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60794
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60801  -> FStar_Pervasives_Native.Some _60801)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60804)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____60821 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60821
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60828  -> FStar_Pervasives_Native.Some _60828)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____60831)::(bv,uu____60833)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____60854 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60854
            (fun bv1  ->
               let uu____60860 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____60860
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _60867  -> FStar_Pervasives_Native.Some _60867)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____60868 ->
          ((let uu____60870 =
              let uu____60876 =
                let uu____60878 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____60878
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____60876)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____60870);
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
    let uu____60919 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____60919
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____60950 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____60950 e_aqualv
  
let rec unlazy_as_t :
  'Auu____60960 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____60960
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____60973;
             FStar_Syntax_Syntax.rng = uu____60974;_},uu____60975)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____60994 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61032 =
            let uu____61039 =
              let uu____61044 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61044  in
            [uu____61039]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____61032
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____61054 =
            let uu____61061 =
              let uu____61066 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61066  in
            [uu____61061]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____61054
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61076 =
            let uu____61083 =
              let uu____61088 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61088  in
            [uu____61083]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____61076
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61099 =
            let uu____61106 =
              let uu____61111 =
                let uu____61112 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61112 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____61111  in
            let uu____61115 =
              let uu____61122 =
                let uu____61127 =
                  let uu____61128 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61128 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____61127  in
              [uu____61122]  in
            uu____61106 :: uu____61115  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____61099
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____61153 =
            let uu____61160 =
              let uu____61165 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61165  in
            let uu____61166 =
              let uu____61173 =
                let uu____61178 =
                  let uu____61179 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61179 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61178  in
              [uu____61173]  in
            uu____61160 :: uu____61166  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____61153
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61196 =
            let uu____61203 =
              let uu____61208 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61208  in
            let uu____61209 =
              let uu____61216 =
                let uu____61221 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61221  in
              [uu____61216]  in
            uu____61203 :: uu____61209  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____61196
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61235 =
            let uu____61242 =
              let uu____61247 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61247  in
            [uu____61242]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____61235
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____61258 =
            let uu____61265 =
              let uu____61270 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61270  in
            let uu____61271 =
              let uu____61278 =
                let uu____61283 =
                  let uu____61284 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61284 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61283  in
              [uu____61278]  in
            uu____61265 :: uu____61271  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____61258
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61300 =
            let uu____61307 =
              let uu____61312 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61312  in
            [uu____61307]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____61300
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61323 =
            let uu____61330 =
              let uu____61335 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61335  in
            let uu____61336 =
              let uu____61343 =
                let uu____61348 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61348  in
              [uu____61343]  in
            uu____61330 :: uu____61336  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____61323
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____61371 =
            let uu____61378 =
              let uu____61383 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61383  in
            let uu____61385 =
              let uu____61392 =
                let uu____61397 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61397  in
              let uu____61398 =
                let uu____61405 =
                  let uu____61410 =
                    let uu____61411 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____61411 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61410  in
                let uu____61414 =
                  let uu____61421 =
                    let uu____61426 =
                      let uu____61427 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____61427 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____61426  in
                  [uu____61421]  in
                uu____61405 :: uu____61414  in
              uu____61392 :: uu____61398  in
            uu____61378 :: uu____61385  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____61371
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____61456 =
            let uu____61463 =
              let uu____61468 =
                let uu____61469 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61469 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____61468  in
            let uu____61472 =
              let uu____61479 =
                let uu____61484 =
                  let uu____61485 =
                    let uu____61494 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____61494  in
                  FStar_TypeChecker_NBETerm.embed uu____61485 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____61484  in
              [uu____61479]  in
            uu____61463 :: uu____61472  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____61456
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____61530 =
            let uu____61537 =
              let uu____61542 =
                let uu____61543 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61543 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61542  in
            let uu____61546 =
              let uu____61553 =
                let uu____61558 =
                  let uu____61559 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61559 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61558  in
              let uu____61562 =
                let uu____61569 =
                  let uu____61574 =
                    let uu____61575 =
                      let uu____61580 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61580  in
                    FStar_TypeChecker_NBETerm.embed uu____61575 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61574  in
                [uu____61569]  in
              uu____61553 :: uu____61562  in
            uu____61537 :: uu____61546  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61530
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____61608 =
            let uu____61615 =
              let uu____61620 =
                let uu____61621 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61621 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61620  in
            let uu____61624 =
              let uu____61631 =
                let uu____61636 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61636  in
              let uu____61637 =
                let uu____61644 =
                  let uu____61649 =
                    let uu____61650 =
                      let uu____61655 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61655  in
                    FStar_TypeChecker_NBETerm.embed uu____61650 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61649  in
                [uu____61644]  in
              uu____61631 :: uu____61637  in
            uu____61615 :: uu____61624  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61608
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61696,(b,uu____61698)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____61717 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61717
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61724  -> FStar_Pervasives_Native.Some _61724)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61726,(b,uu____61728)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____61747 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61747
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61754  -> FStar_Pervasives_Native.Some _61754)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61756,(f,uu____61758)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____61777 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____61777
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _61784  -> FStar_Pervasives_Native.Some _61784)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61786,(r,uu____61788)::(l,uu____61790)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____61813 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____61813
            (fun l1  ->
               let uu____61819 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____61819
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _61826  -> FStar_Pervasives_Native.Some _61826)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61828,(t1,uu____61830)::(b,uu____61832)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____61855 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61855
            (fun b1  ->
               let uu____61861 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61861
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _61868  -> FStar_Pervasives_Native.Some _61868)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61870,(t1,uu____61872)::(b,uu____61874)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____61897 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61897
            (fun b1  ->
               let uu____61903 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____61903
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _61910  -> FStar_Pervasives_Native.Some _61910)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61912,(u,uu____61914)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____61933 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____61933
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _61940  -> FStar_Pervasives_Native.Some _61940)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61942,(t1,uu____61944)::(b,uu____61946)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____61969 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61969
            (fun b1  ->
               let uu____61975 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61975
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _61982  -> FStar_Pervasives_Native.Some _61982)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61984,(c,uu____61986)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____62005 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____62005
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _62012  -> FStar_Pervasives_Native.Some _62012)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62014,(l,uu____62016)::(u,uu____62018)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____62041 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____62041
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _62050  -> FStar_Pervasives_Native.Some _62050)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62052,(t2,uu____62054)::(t1,uu____62056)::(b,uu____62058)::
           (r,uu____62060)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____62091 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____62091
            (fun r1  ->
               let uu____62101 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____62101
                 (fun b1  ->
                    let uu____62107 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____62107
                      (fun t11  ->
                         let uu____62113 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____62113
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _62120  ->
                                   FStar_Pervasives_Native.Some _62120)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62123,(brs,uu____62125)::(t1,uu____62127)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____62150 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____62150
            (fun t2  ->
               let uu____62156 =
                 let uu____62161 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____62161 cb brs  in
               FStar_Util.bind_opt uu____62156
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _62176  -> FStar_Pervasives_Native.Some _62176)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62180,(tacopt,uu____62182)::(t1,uu____62184)::(e,uu____62186)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____62213 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62213
            (fun e1  ->
               let uu____62219 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____62219
                 (fun t2  ->
                    let uu____62225 =
                      let uu____62230 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62230 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62225
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62245  ->
                              FStar_Pervasives_Native.Some _62245)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62249,(tacopt,uu____62251)::(c,uu____62253)::(e,uu____62255)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____62282 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62282
            (fun e1  ->
               let uu____62288 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____62288
                 (fun c1  ->
                    let uu____62294 =
                      let uu____62299 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62299 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62294
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62314  ->
                              FStar_Pervasives_Native.Some _62314)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____62318,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _62335  -> FStar_Pervasives_Native.Some _62335)
            FStar_Reflection_Data.Tv_Unknown
      | uu____62336 ->
          ((let uu____62338 =
              let uu____62344 =
                let uu____62346 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____62346
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____62344)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____62338);
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
    let uu____62373 =
      let uu____62380 =
        let uu____62385 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____62385  in
      let uu____62387 =
        let uu____62394 =
          let uu____62399 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____62399  in
        let uu____62400 =
          let uu____62407 =
            let uu____62412 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62412  in
          [uu____62407]  in
        uu____62394 :: uu____62400  in
      uu____62380 :: uu____62387  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____62373
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62445,(s,uu____62447)::(idx,uu____62449)::(nm,uu____62451)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____62478 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____62478
          (fun nm1  ->
             let uu____62488 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____62488
               (fun idx1  ->
                  let uu____62494 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____62494
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _62501  -> FStar_Pervasives_Native.Some _62501)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____62502 ->
        ((let uu____62504 =
            let uu____62510 =
              let uu____62512 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____62512
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62510)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62504);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____62536 =
          let uu____62543 =
            let uu____62548 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____62548  in
          let uu____62549 =
            let uu____62556 =
              let uu____62561 =
                let uu____62562 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____62562 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____62561  in
            [uu____62556]  in
          uu____62543 :: uu____62549  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____62536
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____62586 =
          let uu____62593 =
            let uu____62598 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62598  in
          let uu____62599 =
            let uu____62606 =
              let uu____62611 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____62611  in
            [uu____62606]  in
          uu____62593 :: uu____62599  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____62586
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62644,(md,uu____62646)::(t1,uu____62648)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____62671 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____62671
          (fun t2  ->
             let uu____62677 =
               let uu____62682 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____62682 cb md  in
             FStar_Util.bind_opt uu____62677
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _62697  -> FStar_Pervasives_Native.Some _62697)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62701,(post,uu____62703)::(pre,uu____62705)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____62728 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____62728
          (fun pre1  ->
             let uu____62734 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____62734
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _62741  -> FStar_Pervasives_Native.Some _62741)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62743,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _62760  -> FStar_Pervasives_Native.Some _62760)
          FStar_Reflection_Data.C_Unknown
    | uu____62761 ->
        ((let uu____62763 =
            let uu____62769 =
              let uu____62771 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____62771
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62769)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62763);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62817,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62833,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62849,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____62864 ->
        ((let uu____62866 =
            let uu____62872 =
              let uu____62874 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____62874  in
            (FStar_Errors.Warning_NotEmbedded, uu____62872)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62866);
         FStar_Pervasives_Native.None)
     in
  let uu____62878 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____62878 
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
           FStar_Syntax_Syntax.ltyp = uu____62909;
           FStar_Syntax_Syntax.rng = uu____62910;_},uu____62911)
        ->
        let uu____62930 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____62930
    | uu____62931 ->
        ((let uu____62933 =
            let uu____62939 =
              let uu____62941 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____62941  in
            (FStar_Errors.Warning_NotEmbedded, uu____62939)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62933);
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
    let uu____62970 =
      let uu____62976 = FStar_Ident.range_of_id i  in
      let uu____62977 = FStar_Ident.text_of_id i  in
      (uu____62976, uu____62977)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____62970  in
  let unembed_ident cb t =
    let uu____63000 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____63000 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____63024 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____63024
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
    let uu____63034 =
      let uu____63042 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____63044 =
        let uu____63047 = fv_as_emb_typ range_fv  in
        let uu____63048 =
          let uu____63051 = fv_as_emb_typ string_fv  in [uu____63051]  in
        uu____63047 :: uu____63048  in
      (uu____63042, uu____63044)  in
    FStar_Syntax_Syntax.ET_app uu____63034  in
  let uu____63055 =
    let uu____63056 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____63057 =
      let uu____63064 =
        let uu____63069 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____63069  in
      let uu____63074 =
        let uu____63081 =
          let uu____63086 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____63086  in
        [uu____63081]  in
      uu____63064 :: uu____63074  in
    mkFV uu____63056 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____63057
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____63055 et 
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
        let uu____63143 =
          let uu____63150 =
            let uu____63155 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____63155  in
          let uu____63157 =
            let uu____63164 =
              let uu____63169 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63169  in
            let uu____63170 =
              let uu____63177 =
                let uu____63182 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____63182  in
              let uu____63185 =
                let uu____63192 =
                  let uu____63197 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63197  in
                let uu____63198 =
                  let uu____63205 =
                    let uu____63210 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63210  in
                  [uu____63205]  in
                uu____63192 :: uu____63198  in
              uu____63177 :: uu____63185  in
            uu____63164 :: uu____63170  in
          uu____63150 :: uu____63157  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____63143
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____63237 =
          let uu____63244 =
            let uu____63249 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63249  in
          let uu____63253 =
            let uu____63260 =
              let uu____63265 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63265  in
            [uu____63260]  in
          uu____63244 :: uu____63253  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____63237
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____63295 =
          let uu____63302 =
            let uu____63307 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63307  in
          let uu____63311 =
            let uu____63318 =
              let uu____63323 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____63323  in
            let uu____63326 =
              let uu____63333 =
                let uu____63338 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____63338  in
              let uu____63339 =
                let uu____63346 =
                  let uu____63351 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63351  in
                let uu____63352 =
                  let uu____63359 =
                    let uu____63364 =
                      let uu____63365 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____63365 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63364  in
                  [uu____63359]  in
                uu____63346 :: uu____63352  in
              uu____63333 :: uu____63339  in
            uu____63318 :: uu____63326  in
          uu____63302 :: uu____63311  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____63295
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63425,(dcs,uu____63427)::(t1,uu____63429)::(bs,uu____63431)::
         (us,uu____63433)::(nm,uu____63435)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____63470 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____63470
          (fun nm1  ->
             let uu____63488 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____63488
               (fun us1  ->
                  let uu____63502 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____63502
                    (fun bs1  ->
                       let uu____63508 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____63508
                         (fun t2  ->
                            let uu____63514 =
                              let uu____63522 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____63522
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____63514
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _63552  ->
                                      FStar_Pervasives_Native.Some _63552)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63560,(t1,uu____63562)::(ty,uu____63564)::(univs1,uu____63566)::
         (fvar1,uu____63568)::(r,uu____63570)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____63605 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____63605
          (fun r1  ->
             let uu____63615 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____63615
               (fun fvar2  ->
                  let uu____63621 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____63621
                    (fun univs2  ->
                       let uu____63635 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____63635
                         (fun ty1  ->
                            let uu____63641 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____63641
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _63648  ->
                                      FStar_Pervasives_Native.Some _63648)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63653,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____63668 ->
        ((let uu____63670 =
            let uu____63676 =
              let uu____63678 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____63678
               in
            (FStar_Errors.Warning_NotEmbedded, uu____63676)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63670);
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
        let uu____63701 =
          let uu____63708 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____63708]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____63701
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____63723 =
          let uu____63730 =
            let uu____63735 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____63735  in
          let uu____63736 =
            let uu____63743 =
              let uu____63748 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____63748  in
            [uu____63743]  in
          uu____63730 :: uu____63736  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____63723
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63777,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63793,(i,uu____63795)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____63814 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____63814
          (fun i1  ->
             FStar_All.pipe_left
               (fun _63821  -> FStar_Pervasives_Native.Some _63821)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63823,(e2,uu____63825)::(e1,uu____63827)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____63850 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____63850
          (fun e11  ->
             let uu____63856 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____63856
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _63863  -> FStar_Pervasives_Native.Some _63863)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____63864 ->
        ((let uu____63866 =
            let uu____63872 =
              let uu____63874 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____63874  in
            (FStar_Errors.Warning_NotEmbedded, uu____63872)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63866);
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