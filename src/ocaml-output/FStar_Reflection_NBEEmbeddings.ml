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
    let uu____64305 =
      let uu____64313 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____64313, [])  in
    FStar_Syntax_Syntax.ET_app uu____64305
  
let mk_emb' :
  'Auu____64327 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____64327 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____64327 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____64327 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____64369 = mkFV fv [] []  in
        let uu____64374 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____64369 uu____64374
  
let mk_lazy :
  'Auu____64386 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____64386 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____64412 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____64412;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____64418  ->
                 let uu____64419 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____64419)
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
           FStar_Syntax_Syntax.ltyp = uu____64504;
           FStar_Syntax_Syntax.rng = uu____64505;_},uu____64506)
        ->
        let uu____64525 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64528  -> FStar_Pervasives_Native.Some _64528) uu____64525
    | uu____64529 ->
        ((let uu____64531 =
            let uu____64537 =
              let uu____64539 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____64539  in
            (FStar_Errors.Warning_NotEmbedded, uu____64537)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64531);
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
           FStar_Syntax_Syntax.ltyp = uu____64573;
           FStar_Syntax_Syntax.rng = uu____64574;_},uu____64575)
        ->
        let uu____64594 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64594
    | uu____64595 ->
        ((let uu____64597 =
            let uu____64603 =
              let uu____64605 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____64605  in
            (FStar_Errors.Warning_NotEmbedded, uu____64603)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64597);
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
          let uu____64655 = f x  in
          FStar_Util.bind_opt uu____64655
            (fun x1  ->
               let uu____64663 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64663
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
      | uu____64733 -> FStar_Pervasives_Native.None  in
    let uu____64734 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____64739 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____64734;
      FStar_TypeChecker_NBETerm.emb_typ = uu____64739
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
        let uu____64772 =
          let uu____64779 =
            let uu____64784 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____64784  in
          [uu____64779]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____64772
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____64836)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____64853 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____64853
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____64858 ->
        ((let uu____64860 =
            let uu____64866 =
              let uu____64868 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____64868  in
            (FStar_Errors.Warning_NotEmbedded, uu____64866)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64860);
         FStar_Pervasives_Native.None)
     in
  let uu____64872 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____64877 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____64872
    uu____64877
  
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
           FStar_Syntax_Syntax.ltyp = uu____64911;
           FStar_Syntax_Syntax.rng = uu____64912;_},uu____64913)
        ->
        let uu____64932 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64932
    | uu____64933 ->
        ((let uu____64935 =
            let uu____64941 =
              let uu____64943 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____64943  in
            (FStar_Errors.Warning_NotEmbedded, uu____64941)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64935);
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
           FStar_Syntax_Syntax.ltyp = uu____64977;
           FStar_Syntax_Syntax.rng = uu____64978;_},uu____64979)
        ->
        let uu____64998 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64998
    | uu____64999 ->
        ((let uu____65001 =
            let uu____65007 =
              let uu____65009 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____65009  in
            (FStar_Errors.Warning_NotEmbedded, uu____65007)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65001);
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
           FStar_Syntax_Syntax.ltyp = uu____65043;
           FStar_Syntax_Syntax.rng = uu____65044;_},uu____65045)
        ->
        let uu____65064 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65064
    | uu____65065 ->
        ((let uu____65067 =
            let uu____65073 =
              let uu____65075 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____65075  in
            (FStar_Errors.Warning_NotEmbedded, uu____65073)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65067);
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
        let uu____65106 =
          let uu____65113 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____65113]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____65106
    | FStar_Reflection_Data.C_String s ->
        let uu____65128 =
          let uu____65135 =
            let uu____65140 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65140  in
          [uu____65135]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____65128
    | FStar_Reflection_Data.C_Range r ->
        let uu____65151 =
          let uu____65158 =
            let uu____65163 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65163  in
          [uu____65158]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____65151
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____65177 =
          let uu____65184 =
            let uu____65189 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65189  in
          [uu____65184]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____65177
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____65257)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____65274 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____65274
          (fun i1  ->
             FStar_All.pipe_left
               (fun _65281  -> FStar_Pervasives_Native.Some _65281)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____65284)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____65301 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____65301
          (fun s1  ->
             FStar_All.pipe_left
               (fun _65312  -> FStar_Pervasives_Native.Some _65312)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____65315)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____65332 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____65332
          (fun r1  ->
             FStar_All.pipe_left
               (fun _65339  -> FStar_Pervasives_Native.Some _65339)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____65355)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____65372 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____65372
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _65391  -> FStar_Pervasives_Native.Some _65391)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____65392 ->
        ((let uu____65394 =
            let uu____65400 =
              let uu____65402 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____65402  in
            (FStar_Errors.Warning_NotEmbedded, uu____65400)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65394);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____65413  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65426 =
            let uu____65433 =
              let uu____65438 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65438  in
            [uu____65433]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____65426
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65453 =
            let uu____65460 =
              let uu____65465 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65465  in
            let uu____65466 =
              let uu____65473 =
                let uu____65478 =
                  let uu____65479 =
                    let uu____65484 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____65484  in
                  FStar_TypeChecker_NBETerm.embed uu____65479 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____65478  in
              [uu____65473]  in
            uu____65460 :: uu____65466  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____65453
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65502 =
            let uu____65509 =
              let uu____65514 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65514  in
            [uu____65509]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____65502
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65524 =
            let uu____65531 =
              let uu____65536 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65536  in
            [uu____65531]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____65524
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65547 =
            let uu____65554 =
              let uu____65559 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65559  in
            let uu____65560 =
              let uu____65567 =
                let uu____65572 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____65572  in
              [uu____65567]  in
            uu____65554 :: uu____65560  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____65547
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____65602)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____65619 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____65619
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _65626  -> FStar_Pervasives_Native.Some _65626)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____65629)::(f,uu____65631)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____65652 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____65652
            (fun f1  ->
               let uu____65658 =
                 let uu____65663 =
                   let uu____65668 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____65668  in
                 FStar_TypeChecker_NBETerm.unembed uu____65663 cb ps  in
               FStar_Util.bind_opt uu____65658
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _65681  -> FStar_Pervasives_Native.Some _65681)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65686)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____65703 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65703
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65710  -> FStar_Pervasives_Native.Some _65710)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65713)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____65730 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65730
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65737  -> FStar_Pervasives_Native.Some _65737)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____65740)::(bv,uu____65742)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____65763 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65763
            (fun bv1  ->
               let uu____65769 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____65769
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _65776  -> FStar_Pervasives_Native.Some _65776)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____65777 ->
          ((let uu____65779 =
              let uu____65785 =
                let uu____65787 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____65787
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65785)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____65779);
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
    let uu____65828 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____65828
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____65859 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____65859 e_aqualv
  
let rec unlazy_as_t :
  'Auu____65869 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____65869
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____65882;
             FStar_Syntax_Syntax.rng = uu____65883;_},uu____65884)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____65903 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____65941 =
            let uu____65948 =
              let uu____65953 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65953  in
            [uu____65948]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____65941
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____65963 =
            let uu____65970 =
              let uu____65975 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65975  in
            [uu____65970]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____65963
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____65985 =
            let uu____65992 =
              let uu____65997 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65997  in
            [uu____65992]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____65985
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66008 =
            let uu____66015 =
              let uu____66020 =
                let uu____66021 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66021 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____66020  in
            let uu____66024 =
              let uu____66031 =
                let uu____66036 =
                  let uu____66037 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66037 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____66036  in
              [uu____66031]  in
            uu____66015 :: uu____66024  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____66008
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____66062 =
            let uu____66069 =
              let uu____66074 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66074  in
            let uu____66075 =
              let uu____66082 =
                let uu____66087 =
                  let uu____66088 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66088 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66087  in
              [uu____66082]  in
            uu____66069 :: uu____66075  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____66062
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66105 =
            let uu____66112 =
              let uu____66117 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66117  in
            let uu____66118 =
              let uu____66125 =
                let uu____66130 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66130  in
              [uu____66125]  in
            uu____66112 :: uu____66118  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____66105
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66144 =
            let uu____66151 =
              let uu____66156 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66156  in
            [uu____66151]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____66144
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____66167 =
            let uu____66174 =
              let uu____66179 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66179  in
            let uu____66180 =
              let uu____66187 =
                let uu____66192 =
                  let uu____66193 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66193 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66192  in
              [uu____66187]  in
            uu____66174 :: uu____66180  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____66167
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66209 =
            let uu____66216 =
              let uu____66221 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66221  in
            [uu____66216]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____66209
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66232 =
            let uu____66239 =
              let uu____66244 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66244  in
            let uu____66245 =
              let uu____66252 =
                let uu____66257 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66257  in
              [uu____66252]  in
            uu____66239 :: uu____66245  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____66232
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66280 =
            let uu____66287 =
              let uu____66292 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66292  in
            let uu____66294 =
              let uu____66301 =
                let uu____66306 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66306  in
              let uu____66307 =
                let uu____66314 =
                  let uu____66319 =
                    let uu____66320 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____66320 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66319  in
                let uu____66323 =
                  let uu____66330 =
                    let uu____66335 =
                      let uu____66336 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____66336 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____66335  in
                  [uu____66330]  in
                uu____66314 :: uu____66323  in
              uu____66301 :: uu____66307  in
            uu____66287 :: uu____66294  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____66280
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____66365 =
            let uu____66372 =
              let uu____66377 =
                let uu____66378 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66378 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____66377  in
            let uu____66381 =
              let uu____66388 =
                let uu____66393 =
                  let uu____66394 =
                    let uu____66403 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____66403  in
                  FStar_TypeChecker_NBETerm.embed uu____66394 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____66393  in
              [uu____66388]  in
            uu____66372 :: uu____66381  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____66365
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____66439 =
            let uu____66446 =
              let uu____66451 =
                let uu____66452 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66452 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66451  in
            let uu____66455 =
              let uu____66462 =
                let uu____66467 =
                  let uu____66468 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66468 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66467  in
              let uu____66471 =
                let uu____66478 =
                  let uu____66483 =
                    let uu____66484 =
                      let uu____66489 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66489  in
                    FStar_TypeChecker_NBETerm.embed uu____66484 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66483  in
                [uu____66478]  in
              uu____66462 :: uu____66471  in
            uu____66446 :: uu____66455  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66439
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____66517 =
            let uu____66524 =
              let uu____66529 =
                let uu____66530 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66530 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66529  in
            let uu____66533 =
              let uu____66540 =
                let uu____66545 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66545  in
              let uu____66546 =
                let uu____66553 =
                  let uu____66558 =
                    let uu____66559 =
                      let uu____66564 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66564  in
                    FStar_TypeChecker_NBETerm.embed uu____66559 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66558  in
                [uu____66553]  in
              uu____66540 :: uu____66546  in
            uu____66524 :: uu____66533  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66517
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66605,(b,uu____66607)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____66626 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66626
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66633  -> FStar_Pervasives_Native.Some _66633)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66635,(b,uu____66637)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____66656 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66656
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66663  -> FStar_Pervasives_Native.Some _66663)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66665,(f,uu____66667)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____66686 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____66686
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _66693  -> FStar_Pervasives_Native.Some _66693)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66695,(r,uu____66697)::(l,uu____66699)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____66722 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____66722
            (fun l1  ->
               let uu____66728 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____66728
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _66735  -> FStar_Pervasives_Native.Some _66735)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66737,(t1,uu____66739)::(b,uu____66741)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____66764 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66764
            (fun b1  ->
               let uu____66770 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66770
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66777  -> FStar_Pervasives_Native.Some _66777)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66779,(t1,uu____66781)::(b,uu____66783)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____66806 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66806
            (fun b1  ->
               let uu____66812 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____66812
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _66819  -> FStar_Pervasives_Native.Some _66819)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66821,(u,uu____66823)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____66842 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____66842
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _66849  -> FStar_Pervasives_Native.Some _66849)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66851,(t1,uu____66853)::(b,uu____66855)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____66878 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66878
            (fun b1  ->
               let uu____66884 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66884
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66891  -> FStar_Pervasives_Native.Some _66891)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66893,(c,uu____66895)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____66914 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____66914
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _66921  -> FStar_Pervasives_Native.Some _66921)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66923,(l,uu____66925)::(u,uu____66927)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____66950 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____66950
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _66959  -> FStar_Pervasives_Native.Some _66959)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66961,(t2,uu____66963)::(t1,uu____66965)::(b,uu____66967)::
           (r,uu____66969)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____67000 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____67000
            (fun r1  ->
               let uu____67010 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____67010
                 (fun b1  ->
                    let uu____67016 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____67016
                      (fun t11  ->
                         let uu____67022 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____67022
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _67029  ->
                                   FStar_Pervasives_Native.Some _67029)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67032,(brs,uu____67034)::(t1,uu____67036)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____67059 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____67059
            (fun t2  ->
               let uu____67065 =
                 let uu____67070 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____67070 cb brs  in
               FStar_Util.bind_opt uu____67065
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _67085  -> FStar_Pervasives_Native.Some _67085)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67089,(tacopt,uu____67091)::(t1,uu____67093)::(e,uu____67095)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____67122 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67122
            (fun e1  ->
               let uu____67128 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____67128
                 (fun t2  ->
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
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67158,(tacopt,uu____67160)::(c,uu____67162)::(e,uu____67164)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____67191 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67191
            (fun e1  ->
               let uu____67197 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____67197
                 (fun c1  ->
                    let uu____67203 =
                      let uu____67208 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67208 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67203
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67223  ->
                              FStar_Pervasives_Native.Some _67223)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____67227,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _67244  -> FStar_Pervasives_Native.Some _67244)
            FStar_Reflection_Data.Tv_Unknown
      | uu____67245 ->
          ((let uu____67247 =
              let uu____67253 =
                let uu____67255 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____67255
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____67253)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____67247);
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
    let uu____67282 =
      let uu____67289 =
        let uu____67294 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____67294  in
      let uu____67296 =
        let uu____67303 =
          let uu____67308 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____67308  in
        let uu____67309 =
          let uu____67316 =
            let uu____67321 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67321  in
          [uu____67316]  in
        uu____67303 :: uu____67309  in
      uu____67289 :: uu____67296  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____67282
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67354,(s,uu____67356)::(idx,uu____67358)::(nm,uu____67360)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____67387 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____67387
          (fun nm1  ->
             let uu____67397 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____67397
               (fun idx1  ->
                  let uu____67403 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____67403
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _67410  -> FStar_Pervasives_Native.Some _67410)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____67411 ->
        ((let uu____67413 =
            let uu____67419 =
              let uu____67421 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____67421
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67419)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67413);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____67445 =
          let uu____67452 =
            let uu____67457 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____67457  in
          let uu____67458 =
            let uu____67465 =
              let uu____67470 =
                let uu____67471 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____67471 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____67470  in
            [uu____67465]  in
          uu____67452 :: uu____67458  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____67445
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____67495 =
          let uu____67502 =
            let uu____67507 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67507  in
          let uu____67508 =
            let uu____67515 =
              let uu____67520 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____67520  in
            [uu____67515]  in
          uu____67502 :: uu____67508  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____67495
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67553,(md,uu____67555)::(t1,uu____67557)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____67580 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____67580
          (fun t2  ->
             let uu____67586 =
               let uu____67591 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____67591 cb md  in
             FStar_Util.bind_opt uu____67586
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _67606  -> FStar_Pervasives_Native.Some _67606)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67610,(post,uu____67612)::(pre,uu____67614)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____67637 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____67637
          (fun pre1  ->
             let uu____67643 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____67643
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _67650  -> FStar_Pervasives_Native.Some _67650)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67652,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _67669  -> FStar_Pervasives_Native.Some _67669)
          FStar_Reflection_Data.C_Unknown
    | uu____67670 ->
        ((let uu____67672 =
            let uu____67678 =
              let uu____67680 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____67680
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67678)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67672);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67726,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67742,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67758,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____67773 ->
        ((let uu____67775 =
            let uu____67781 =
              let uu____67783 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____67783  in
            (FStar_Errors.Warning_NotEmbedded, uu____67781)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67775);
         FStar_Pervasives_Native.None)
     in
  let uu____67787 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____67787 
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
           FStar_Syntax_Syntax.ltyp = uu____67818;
           FStar_Syntax_Syntax.rng = uu____67819;_},uu____67820)
        ->
        let uu____67839 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____67839
    | uu____67840 ->
        ((let uu____67842 =
            let uu____67848 =
              let uu____67850 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____67850  in
            (FStar_Errors.Warning_NotEmbedded, uu____67848)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67842);
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
    let uu____67879 =
      let uu____67885 = FStar_Ident.range_of_id i  in
      let uu____67886 = FStar_Ident.text_of_id i  in
      (uu____67885, uu____67886)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____67879  in
  let unembed_ident cb t =
    let uu____67909 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____67909 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____67933 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____67933
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
    let uu____67943 =
      let uu____67951 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____67953 =
        let uu____67956 = fv_as_emb_typ range_fv  in
        let uu____67957 =
          let uu____67960 = fv_as_emb_typ string_fv  in [uu____67960]  in
        uu____67956 :: uu____67957  in
      (uu____67951, uu____67953)  in
    FStar_Syntax_Syntax.ET_app uu____67943  in
  let uu____67964 =
    let uu____67965 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____67966 =
      let uu____67973 =
        let uu____67978 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____67978  in
      let uu____67983 =
        let uu____67990 =
          let uu____67995 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____67995  in
        [uu____67990]  in
      uu____67973 :: uu____67983  in
    mkFV uu____67965 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____67966
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____67964 et 
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
        let uu____68052 =
          let uu____68059 =
            let uu____68064 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____68064  in
          let uu____68066 =
            let uu____68073 =
              let uu____68078 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68078  in
            let uu____68079 =
              let uu____68086 =
                let uu____68091 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____68091  in
              let uu____68094 =
                let uu____68101 =
                  let uu____68106 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68106  in
                let uu____68107 =
                  let uu____68114 =
                    let uu____68119 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68119  in
                  [uu____68114]  in
                uu____68101 :: uu____68107  in
              uu____68086 :: uu____68094  in
            uu____68073 :: uu____68079  in
          uu____68059 :: uu____68066  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____68052
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____68146 =
          let uu____68153 =
            let uu____68158 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68158  in
          let uu____68162 =
            let uu____68169 =
              let uu____68174 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68174  in
            [uu____68169]  in
          uu____68153 :: uu____68162  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____68146
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____68204 =
          let uu____68211 =
            let uu____68216 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68216  in
          let uu____68220 =
            let uu____68227 =
              let uu____68232 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____68232  in
            let uu____68235 =
              let uu____68242 =
                let uu____68247 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____68247  in
              let uu____68248 =
                let uu____68255 =
                  let uu____68260 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68260  in
                let uu____68261 =
                  let uu____68268 =
                    let uu____68273 =
                      let uu____68274 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____68274 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68273  in
                  [uu____68268]  in
                uu____68255 :: uu____68261  in
              uu____68242 :: uu____68248  in
            uu____68227 :: uu____68235  in
          uu____68211 :: uu____68220  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____68204
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68334,(dcs,uu____68336)::(t1,uu____68338)::(bs,uu____68340)::
         (us,uu____68342)::(nm,uu____68344)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____68379 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____68379
          (fun nm1  ->
             let uu____68397 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____68397
               (fun us1  ->
                  let uu____68411 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____68411
                    (fun bs1  ->
                       let uu____68417 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____68417
                         (fun t2  ->
                            let uu____68423 =
                              let uu____68431 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____68431
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____68423
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _68461  ->
                                      FStar_Pervasives_Native.Some _68461)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68469,(t1,uu____68471)::(ty,uu____68473)::(univs1,uu____68475)::
         (fvar1,uu____68477)::(r,uu____68479)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____68514 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____68514
          (fun r1  ->
             let uu____68524 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____68524
               (fun fvar2  ->
                  let uu____68530 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____68530
                    (fun univs2  ->
                       let uu____68544 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____68544
                         (fun ty1  ->
                            let uu____68550 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____68550
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _68557  ->
                                      FStar_Pervasives_Native.Some _68557)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68562,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____68577 ->
        ((let uu____68579 =
            let uu____68585 =
              let uu____68587 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____68587
               in
            (FStar_Errors.Warning_NotEmbedded, uu____68585)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68579);
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
        let uu____68610 =
          let uu____68617 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____68617]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____68610
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____68632 =
          let uu____68639 =
            let uu____68644 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____68644  in
          let uu____68645 =
            let uu____68652 =
              let uu____68657 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____68657  in
            [uu____68652]  in
          uu____68639 :: uu____68645  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____68632
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68686,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68702,(i,uu____68704)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____68723 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____68723
          (fun i1  ->
             FStar_All.pipe_left
               (fun _68730  -> FStar_Pervasives_Native.Some _68730)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68732,(e2,uu____68734)::(e1,uu____68736)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____68759 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____68759
          (fun e11  ->
             let uu____68765 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____68765
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _68772  -> FStar_Pervasives_Native.Some _68772)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____68773 ->
        ((let uu____68775 =
            let uu____68781 =
              let uu____68783 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____68783  in
            (FStar_Errors.Warning_NotEmbedded, uu____68781)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68775);
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