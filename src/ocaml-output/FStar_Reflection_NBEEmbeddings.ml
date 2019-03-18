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
    let uu____59422 =
      let uu____59430 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____59430, [])  in
    FStar_Syntax_Syntax.ET_app uu____59422
  
let mk_emb' :
  'Auu____59444 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____59444 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____59444 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____59444 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____59486 = mkFV fv [] []  in
        let uu____59491 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____59486 uu____59491
  
let mk_lazy :
  'Auu____59503 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____59503 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____59529 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____59529;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____59535  ->
                 let uu____59536 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____59536)
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
           FStar_Syntax_Syntax.ltyp = uu____59581;
           FStar_Syntax_Syntax.rng = uu____59582;_},uu____59583)
        ->
        let uu____59602 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _59605  -> FStar_Pervasives_Native.Some _59605) uu____59602
    | uu____59606 ->
        ((let uu____59608 =
            let uu____59614 =
              let uu____59616 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____59616  in
            (FStar_Errors.Warning_NotEmbedded, uu____59614)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59608);
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
           FStar_Syntax_Syntax.ltyp = uu____59650;
           FStar_Syntax_Syntax.rng = uu____59651;_},uu____59652)
        ->
        let uu____59671 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59671
    | uu____59672 ->
        ((let uu____59674 =
            let uu____59680 =
              let uu____59682 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____59682  in
            (FStar_Errors.Warning_NotEmbedded, uu____59680)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59674);
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
          let uu____59732 = f x  in
          FStar_Util.bind_opt uu____59732
            (fun x1  ->
               let uu____59740 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59740
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
      | uu____59810 -> FStar_Pervasives_Native.None  in
    let uu____59811 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____59816 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____59811;
      FStar_TypeChecker_NBETerm.emb_typ = uu____59816
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
        let uu____59849 =
          let uu____59856 =
            let uu____59861 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____59861  in
          [uu____59856]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____59849
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____59913)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____59930 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____59930
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____59935 ->
        ((let uu____59937 =
            let uu____59943 =
              let uu____59945 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____59945  in
            (FStar_Errors.Warning_NotEmbedded, uu____59943)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59937);
         FStar_Pervasives_Native.None)
     in
  let uu____59949 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____59954 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____59949
    uu____59954
  
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
           FStar_Syntax_Syntax.ltyp = uu____59988;
           FStar_Syntax_Syntax.rng = uu____59989;_},uu____59990)
        ->
        let uu____60009 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60009
    | uu____60010 ->
        ((let uu____60012 =
            let uu____60018 =
              let uu____60020 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____60020  in
            (FStar_Errors.Warning_NotEmbedded, uu____60018)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60012);
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
           FStar_Syntax_Syntax.ltyp = uu____60054;
           FStar_Syntax_Syntax.rng = uu____60055;_},uu____60056)
        ->
        let uu____60075 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60075
    | uu____60076 ->
        ((let uu____60078 =
            let uu____60084 =
              let uu____60086 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____60086  in
            (FStar_Errors.Warning_NotEmbedded, uu____60084)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60078);
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
           FStar_Syntax_Syntax.ltyp = uu____60120;
           FStar_Syntax_Syntax.rng = uu____60121;_},uu____60122)
        ->
        let uu____60141 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60141
    | uu____60142 ->
        ((let uu____60144 =
            let uu____60150 =
              let uu____60152 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____60152  in
            (FStar_Errors.Warning_NotEmbedded, uu____60150)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60144);
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
        let uu____60183 =
          let uu____60190 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____60190]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____60183
    | FStar_Reflection_Data.C_String s ->
        let uu____60205 =
          let uu____60212 =
            let uu____60217 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60217  in
          [uu____60212]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____60205
    | FStar_Reflection_Data.C_Range r ->
        let uu____60228 =
          let uu____60235 =
            let uu____60240 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60240  in
          [uu____60235]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____60228
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____60254 =
          let uu____60261 =
            let uu____60266 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60266  in
          [uu____60261]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____60254
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____60334)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____60351 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____60351
          (fun i1  ->
             FStar_All.pipe_left
               (fun _60358  -> FStar_Pervasives_Native.Some _60358)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____60361)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____60378 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____60378
          (fun s1  ->
             FStar_All.pipe_left
               (fun _60389  -> FStar_Pervasives_Native.Some _60389)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____60392)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____60409 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____60409
          (fun r1  ->
             FStar_All.pipe_left
               (fun _60416  -> FStar_Pervasives_Native.Some _60416)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____60432)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____60449 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____60449
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _60468  -> FStar_Pervasives_Native.Some _60468)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____60469 ->
        ((let uu____60471 =
            let uu____60477 =
              let uu____60479 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____60479  in
            (FStar_Errors.Warning_NotEmbedded, uu____60477)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60471);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____60490  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60503 =
            let uu____60510 =
              let uu____60515 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60515  in
            [uu____60510]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____60503
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60530 =
            let uu____60537 =
              let uu____60542 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60542  in
            let uu____60543 =
              let uu____60550 =
                let uu____60555 =
                  let uu____60556 =
                    let uu____60561 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____60561  in
                  FStar_TypeChecker_NBETerm.embed uu____60556 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____60555  in
              [uu____60550]  in
            uu____60537 :: uu____60543  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____60530
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60579 =
            let uu____60586 =
              let uu____60591 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60591  in
            [uu____60586]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____60579
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____60601 =
            let uu____60608 =
              let uu____60613 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60613  in
            [uu____60608]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____60601
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____60624 =
            let uu____60631 =
              let uu____60636 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60636  in
            let uu____60637 =
              let uu____60644 =
                let uu____60649 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____60649  in
              [uu____60644]  in
            uu____60631 :: uu____60637  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____60624
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____60679)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____60696 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____60696
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _60703  -> FStar_Pervasives_Native.Some _60703)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____60706)::(f,uu____60708)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____60729 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____60729
            (fun f1  ->
               let uu____60735 =
                 let uu____60740 =
                   let uu____60745 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____60745  in
                 FStar_TypeChecker_NBETerm.unembed uu____60740 cb ps  in
               FStar_Util.bind_opt uu____60735
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _60758  -> FStar_Pervasives_Native.Some _60758)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60763)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____60780 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60780
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60787  -> FStar_Pervasives_Native.Some _60787)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60790)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____60807 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60807
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60814  -> FStar_Pervasives_Native.Some _60814)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____60817)::(bv,uu____60819)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____60840 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60840
            (fun bv1  ->
               let uu____60846 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____60846
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _60853  -> FStar_Pervasives_Native.Some _60853)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____60854 ->
          ((let uu____60856 =
              let uu____60862 =
                let uu____60864 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____60864
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____60862)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____60856);
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
    let uu____60905 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____60905
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____60936 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____60936 e_aqualv
  
let rec unlazy_as_t :
  'Auu____60946 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____60946
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____60959;
             FStar_Syntax_Syntax.rng = uu____60960;_},uu____60961)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____60980 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61018 =
            let uu____61025 =
              let uu____61030 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61030  in
            [uu____61025]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____61018
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____61040 =
            let uu____61047 =
              let uu____61052 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61052  in
            [uu____61047]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____61040
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61062 =
            let uu____61069 =
              let uu____61074 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61074  in
            [uu____61069]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____61062
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61085 =
            let uu____61092 =
              let uu____61097 =
                let uu____61098 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61098 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____61097  in
            let uu____61101 =
              let uu____61108 =
                let uu____61113 =
                  let uu____61114 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61114 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____61113  in
              [uu____61108]  in
            uu____61092 :: uu____61101  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____61085
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____61139 =
            let uu____61146 =
              let uu____61151 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61151  in
            let uu____61152 =
              let uu____61159 =
                let uu____61164 =
                  let uu____61165 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61165 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61164  in
              [uu____61159]  in
            uu____61146 :: uu____61152  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____61139
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61182 =
            let uu____61189 =
              let uu____61194 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61194  in
            let uu____61195 =
              let uu____61202 =
                let uu____61207 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61207  in
              [uu____61202]  in
            uu____61189 :: uu____61195  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____61182
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61221 =
            let uu____61228 =
              let uu____61233 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61233  in
            [uu____61228]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____61221
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____61244 =
            let uu____61251 =
              let uu____61256 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61256  in
            let uu____61257 =
              let uu____61264 =
                let uu____61269 =
                  let uu____61270 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61270 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61269  in
              [uu____61264]  in
            uu____61251 :: uu____61257  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____61244
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61286 =
            let uu____61293 =
              let uu____61298 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61298  in
            [uu____61293]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____61286
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61309 =
            let uu____61316 =
              let uu____61321 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61321  in
            let uu____61322 =
              let uu____61329 =
                let uu____61334 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61334  in
              [uu____61329]  in
            uu____61316 :: uu____61322  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____61309
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____61357 =
            let uu____61364 =
              let uu____61369 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61369  in
            let uu____61371 =
              let uu____61378 =
                let uu____61383 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61383  in
              let uu____61384 =
                let uu____61391 =
                  let uu____61396 =
                    let uu____61397 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____61397 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61396  in
                let uu____61400 =
                  let uu____61407 =
                    let uu____61412 =
                      let uu____61413 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____61413 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____61412  in
                  [uu____61407]  in
                uu____61391 :: uu____61400  in
              uu____61378 :: uu____61384  in
            uu____61364 :: uu____61371  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____61357
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____61442 =
            let uu____61449 =
              let uu____61454 =
                let uu____61455 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61455 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____61454  in
            let uu____61458 =
              let uu____61465 =
                let uu____61470 =
                  let uu____61471 =
                    let uu____61480 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____61480  in
                  FStar_TypeChecker_NBETerm.embed uu____61471 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____61470  in
              [uu____61465]  in
            uu____61449 :: uu____61458  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____61442
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____61516 =
            let uu____61523 =
              let uu____61528 =
                let uu____61529 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61529 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61528  in
            let uu____61532 =
              let uu____61539 =
                let uu____61544 =
                  let uu____61545 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61545 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61544  in
              let uu____61548 =
                let uu____61555 =
                  let uu____61560 =
                    let uu____61561 =
                      let uu____61566 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61566  in
                    FStar_TypeChecker_NBETerm.embed uu____61561 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61560  in
                [uu____61555]  in
              uu____61539 :: uu____61548  in
            uu____61523 :: uu____61532  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61516
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____61594 =
            let uu____61601 =
              let uu____61606 =
                let uu____61607 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61607 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61606  in
            let uu____61610 =
              let uu____61617 =
                let uu____61622 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61622  in
              let uu____61623 =
                let uu____61630 =
                  let uu____61635 =
                    let uu____61636 =
                      let uu____61641 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61641  in
                    FStar_TypeChecker_NBETerm.embed uu____61636 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61635  in
                [uu____61630]  in
              uu____61617 :: uu____61623  in
            uu____61601 :: uu____61610  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61594
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61682,(b,uu____61684)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____61703 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61703
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61710  -> FStar_Pervasives_Native.Some _61710)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61712,(b,uu____61714)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____61733 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61733
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61740  -> FStar_Pervasives_Native.Some _61740)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61742,(f,uu____61744)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____61763 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____61763
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _61770  -> FStar_Pervasives_Native.Some _61770)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61772,(r,uu____61774)::(l,uu____61776)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____61799 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____61799
            (fun l1  ->
               let uu____61805 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____61805
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _61812  -> FStar_Pervasives_Native.Some _61812)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61814,(t1,uu____61816)::(b,uu____61818)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____61841 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61841
            (fun b1  ->
               let uu____61847 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61847
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _61854  -> FStar_Pervasives_Native.Some _61854)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61856,(t1,uu____61858)::(b,uu____61860)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____61883 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61883
            (fun b1  ->
               let uu____61889 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____61889
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _61896  -> FStar_Pervasives_Native.Some _61896)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61898,(u,uu____61900)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____61919 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____61919
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _61926  -> FStar_Pervasives_Native.Some _61926)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61928,(t1,uu____61930)::(b,uu____61932)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____61955 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61955
            (fun b1  ->
               let uu____61961 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61961
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _61968  -> FStar_Pervasives_Native.Some _61968)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61970,(c,uu____61972)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____61991 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____61991
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _61998  -> FStar_Pervasives_Native.Some _61998)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62000,(l,uu____62002)::(u,uu____62004)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____62027 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____62027
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _62036  -> FStar_Pervasives_Native.Some _62036)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62038,(t2,uu____62040)::(t1,uu____62042)::(b,uu____62044)::
           (r,uu____62046)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____62077 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____62077
            (fun r1  ->
               let uu____62087 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____62087
                 (fun b1  ->
                    let uu____62093 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____62093
                      (fun t11  ->
                         let uu____62099 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____62099
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _62106  ->
                                   FStar_Pervasives_Native.Some _62106)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62109,(brs,uu____62111)::(t1,uu____62113)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____62136 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____62136
            (fun t2  ->
               let uu____62142 =
                 let uu____62147 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____62147 cb brs  in
               FStar_Util.bind_opt uu____62142
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _62162  -> FStar_Pervasives_Native.Some _62162)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62166,(tacopt,uu____62168)::(t1,uu____62170)::(e,uu____62172)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____62199 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62199
            (fun e1  ->
               let uu____62205 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____62205
                 (fun t2  ->
                    let uu____62211 =
                      let uu____62216 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62216 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62211
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62231  ->
                              FStar_Pervasives_Native.Some _62231)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62235,(tacopt,uu____62237)::(c,uu____62239)::(e,uu____62241)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____62268 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62268
            (fun e1  ->
               let uu____62274 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____62274
                 (fun c1  ->
                    let uu____62280 =
                      let uu____62285 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62285 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62280
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62300  ->
                              FStar_Pervasives_Native.Some _62300)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____62304,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _62321  -> FStar_Pervasives_Native.Some _62321)
            FStar_Reflection_Data.Tv_Unknown
      | uu____62322 ->
          ((let uu____62324 =
              let uu____62330 =
                let uu____62332 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____62332
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____62330)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____62324);
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
    let uu____62359 =
      let uu____62366 =
        let uu____62371 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____62371  in
      let uu____62373 =
        let uu____62380 =
          let uu____62385 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____62385  in
        let uu____62386 =
          let uu____62393 =
            let uu____62398 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62398  in
          [uu____62393]  in
        uu____62380 :: uu____62386  in
      uu____62366 :: uu____62373  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____62359
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62431,(s,uu____62433)::(idx,uu____62435)::(nm,uu____62437)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____62464 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____62464
          (fun nm1  ->
             let uu____62474 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____62474
               (fun idx1  ->
                  let uu____62480 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____62480
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _62487  -> FStar_Pervasives_Native.Some _62487)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____62488 ->
        ((let uu____62490 =
            let uu____62496 =
              let uu____62498 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____62498
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62496)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62490);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____62522 =
          let uu____62529 =
            let uu____62534 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____62534  in
          let uu____62535 =
            let uu____62542 =
              let uu____62547 =
                let uu____62548 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____62548 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____62547  in
            [uu____62542]  in
          uu____62529 :: uu____62535  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____62522
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____62572 =
          let uu____62579 =
            let uu____62584 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62584  in
          let uu____62585 =
            let uu____62592 =
              let uu____62597 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____62597  in
            [uu____62592]  in
          uu____62579 :: uu____62585  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____62572
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62630,(md,uu____62632)::(t1,uu____62634)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____62657 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____62657
          (fun t2  ->
             let uu____62663 =
               let uu____62668 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____62668 cb md  in
             FStar_Util.bind_opt uu____62663
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _62683  -> FStar_Pervasives_Native.Some _62683)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62687,(post,uu____62689)::(pre,uu____62691)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____62714 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____62714
          (fun pre1  ->
             let uu____62720 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____62720
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _62727  -> FStar_Pervasives_Native.Some _62727)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62729,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _62746  -> FStar_Pervasives_Native.Some _62746)
          FStar_Reflection_Data.C_Unknown
    | uu____62747 ->
        ((let uu____62749 =
            let uu____62755 =
              let uu____62757 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____62757
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62755)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62749);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62803,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62819,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62835,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____62850 ->
        ((let uu____62852 =
            let uu____62858 =
              let uu____62860 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____62860  in
            (FStar_Errors.Warning_NotEmbedded, uu____62858)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62852);
         FStar_Pervasives_Native.None)
     in
  let uu____62864 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____62864 
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
           FStar_Syntax_Syntax.ltyp = uu____62895;
           FStar_Syntax_Syntax.rng = uu____62896;_},uu____62897)
        ->
        let uu____62916 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____62916
    | uu____62917 ->
        ((let uu____62919 =
            let uu____62925 =
              let uu____62927 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____62927  in
            (FStar_Errors.Warning_NotEmbedded, uu____62925)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62919);
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
    let uu____62956 =
      let uu____62962 = FStar_Ident.range_of_id i  in
      let uu____62963 = FStar_Ident.text_of_id i  in
      (uu____62962, uu____62963)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____62956  in
  let unembed_ident cb t =
    let uu____62986 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____62986 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____63010 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____63010
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
    let uu____63020 =
      let uu____63028 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____63030 =
        let uu____63033 = fv_as_emb_typ range_fv  in
        let uu____63034 =
          let uu____63037 = fv_as_emb_typ string_fv  in [uu____63037]  in
        uu____63033 :: uu____63034  in
      (uu____63028, uu____63030)  in
    FStar_Syntax_Syntax.ET_app uu____63020  in
  let uu____63041 =
    let uu____63042 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____63043 =
      let uu____63050 =
        let uu____63055 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____63055  in
      let uu____63060 =
        let uu____63067 =
          let uu____63072 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____63072  in
        [uu____63067]  in
      uu____63050 :: uu____63060  in
    mkFV uu____63042 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____63043
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____63041 et 
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
        let uu____63129 =
          let uu____63136 =
            let uu____63141 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____63141  in
          let uu____63143 =
            let uu____63150 =
              let uu____63155 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63155  in
            let uu____63156 =
              let uu____63163 =
                let uu____63168 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____63168  in
              let uu____63171 =
                let uu____63178 =
                  let uu____63183 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63183  in
                let uu____63184 =
                  let uu____63191 =
                    let uu____63196 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63196  in
                  [uu____63191]  in
                uu____63178 :: uu____63184  in
              uu____63163 :: uu____63171  in
            uu____63150 :: uu____63156  in
          uu____63136 :: uu____63143  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____63129
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____63223 =
          let uu____63230 =
            let uu____63235 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63235  in
          let uu____63239 =
            let uu____63246 =
              let uu____63251 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63251  in
            [uu____63246]  in
          uu____63230 :: uu____63239  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____63223
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____63281 =
          let uu____63288 =
            let uu____63293 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63293  in
          let uu____63297 =
            let uu____63304 =
              let uu____63309 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____63309  in
            let uu____63312 =
              let uu____63319 =
                let uu____63324 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____63324  in
              let uu____63325 =
                let uu____63332 =
                  let uu____63337 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63337  in
                let uu____63338 =
                  let uu____63345 =
                    let uu____63350 =
                      let uu____63351 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____63351 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63350  in
                  [uu____63345]  in
                uu____63332 :: uu____63338  in
              uu____63319 :: uu____63325  in
            uu____63304 :: uu____63312  in
          uu____63288 :: uu____63297  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____63281
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63411,(dcs,uu____63413)::(t1,uu____63415)::(bs,uu____63417)::
         (us,uu____63419)::(nm,uu____63421)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____63456 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____63456
          (fun nm1  ->
             let uu____63474 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____63474
               (fun us1  ->
                  let uu____63488 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____63488
                    (fun bs1  ->
                       let uu____63494 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____63494
                         (fun t2  ->
                            let uu____63500 =
                              let uu____63508 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____63508
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____63500
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _63538  ->
                                      FStar_Pervasives_Native.Some _63538)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63546,(t1,uu____63548)::(ty,uu____63550)::(univs1,uu____63552)::
         (fvar1,uu____63554)::(r,uu____63556)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____63591 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____63591
          (fun r1  ->
             let uu____63601 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____63601
               (fun fvar2  ->
                  let uu____63607 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____63607
                    (fun univs2  ->
                       let uu____63621 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____63621
                         (fun ty1  ->
                            let uu____63627 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____63627
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _63634  ->
                                      FStar_Pervasives_Native.Some _63634)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63639,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____63654 ->
        ((let uu____63656 =
            let uu____63662 =
              let uu____63664 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____63664
               in
            (FStar_Errors.Warning_NotEmbedded, uu____63662)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63656);
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
        let uu____63687 =
          let uu____63694 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____63694]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____63687
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____63709 =
          let uu____63716 =
            let uu____63721 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____63721  in
          let uu____63722 =
            let uu____63729 =
              let uu____63734 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____63734  in
            [uu____63729]  in
          uu____63716 :: uu____63722  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____63709
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63763,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63779,(i,uu____63781)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____63800 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____63800
          (fun i1  ->
             FStar_All.pipe_left
               (fun _63807  -> FStar_Pervasives_Native.Some _63807)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63809,(e2,uu____63811)::(e1,uu____63813)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____63836 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____63836
          (fun e11  ->
             let uu____63842 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____63842
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _63849  -> FStar_Pervasives_Native.Some _63849)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____63850 ->
        ((let uu____63852 =
            let uu____63858 =
              let uu____63860 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____63860  in
            (FStar_Errors.Warning_NotEmbedded, uu____63858)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63852);
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