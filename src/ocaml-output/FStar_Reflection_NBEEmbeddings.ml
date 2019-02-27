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
    let uu____64241 =
      let uu____64249 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____64249, [])  in
    FStar_Syntax_Syntax.ET_app uu____64241
  
let mk_emb' :
  'Auu____64263 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____64263 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____64263 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____64263 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____64305 = mkFV fv [] []  in
        let uu____64310 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____64305 uu____64310
  
let mk_lazy :
  'Auu____64322 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____64322 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____64348 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____64348;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____64354  ->
                 let uu____64355 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____64355)
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
           FStar_Syntax_Syntax.ltyp = uu____64440;
           FStar_Syntax_Syntax.rng = uu____64441;_},uu____64442)
        ->
        let uu____64461 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64464  -> FStar_Pervasives_Native.Some _64464) uu____64461
    | uu____64465 ->
        ((let uu____64467 =
            let uu____64473 =
              let uu____64475 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____64475  in
            (FStar_Errors.Warning_NotEmbedded, uu____64473)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64467);
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
           FStar_Syntax_Syntax.ltyp = uu____64509;
           FStar_Syntax_Syntax.rng = uu____64510;_},uu____64511)
        ->
        let uu____64530 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64530
    | uu____64531 ->
        ((let uu____64533 =
            let uu____64539 =
              let uu____64541 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____64541  in
            (FStar_Errors.Warning_NotEmbedded, uu____64539)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64533);
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
          let uu____64591 = f x  in
          FStar_Util.bind_opt uu____64591
            (fun x1  ->
               let uu____64599 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64599
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
      | uu____64669 -> FStar_Pervasives_Native.None  in
    let uu____64670 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____64675 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____64670;
      FStar_TypeChecker_NBETerm.emb_typ = uu____64675
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
        let uu____64708 =
          let uu____64715 =
            let uu____64720 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____64720  in
          [uu____64715]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____64708
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____64772)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____64789 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____64789
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____64794 ->
        ((let uu____64796 =
            let uu____64802 =
              let uu____64804 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____64804  in
            (FStar_Errors.Warning_NotEmbedded, uu____64802)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64796);
         FStar_Pervasives_Native.None)
     in
  let uu____64808 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____64813 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____64808
    uu____64813
  
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
           FStar_Syntax_Syntax.ltyp = uu____64847;
           FStar_Syntax_Syntax.rng = uu____64848;_},uu____64849)
        ->
        let uu____64868 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64868
    | uu____64869 ->
        ((let uu____64871 =
            let uu____64877 =
              let uu____64879 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____64879  in
            (FStar_Errors.Warning_NotEmbedded, uu____64877)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64871);
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
           FStar_Syntax_Syntax.ltyp = uu____64913;
           FStar_Syntax_Syntax.rng = uu____64914;_},uu____64915)
        ->
        let uu____64934 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64934
    | uu____64935 ->
        ((let uu____64937 =
            let uu____64943 =
              let uu____64945 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____64945  in
            (FStar_Errors.Warning_NotEmbedded, uu____64943)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64937);
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
           FStar_Syntax_Syntax.ltyp = uu____64979;
           FStar_Syntax_Syntax.rng = uu____64980;_},uu____64981)
        ->
        let uu____65000 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65000
    | uu____65001 ->
        ((let uu____65003 =
            let uu____65009 =
              let uu____65011 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____65011  in
            (FStar_Errors.Warning_NotEmbedded, uu____65009)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65003);
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
        let uu____65042 =
          let uu____65049 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____65049]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____65042
    | FStar_Reflection_Data.C_String s ->
        let uu____65064 =
          let uu____65071 =
            let uu____65076 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65076  in
          [uu____65071]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____65064
    | FStar_Reflection_Data.C_Range r ->
        let uu____65087 =
          let uu____65094 =
            let uu____65099 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65099  in
          [uu____65094]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____65087
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____65113 =
          let uu____65120 =
            let uu____65125 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65125  in
          [uu____65120]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____65113
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____65193)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____65210 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____65210
          (fun i1  ->
             FStar_All.pipe_left
               (fun _65217  -> FStar_Pervasives_Native.Some _65217)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____65220)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____65237 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____65237
          (fun s1  ->
             FStar_All.pipe_left
               (fun _65248  -> FStar_Pervasives_Native.Some _65248)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____65251)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____65268 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____65268
          (fun r1  ->
             FStar_All.pipe_left
               (fun _65275  -> FStar_Pervasives_Native.Some _65275)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____65291)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____65308 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____65308
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _65327  -> FStar_Pervasives_Native.Some _65327)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____65328 ->
        ((let uu____65330 =
            let uu____65336 =
              let uu____65338 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____65338  in
            (FStar_Errors.Warning_NotEmbedded, uu____65336)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65330);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____65349  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65362 =
            let uu____65369 =
              let uu____65374 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65374  in
            [uu____65369]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____65362
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65389 =
            let uu____65396 =
              let uu____65401 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65401  in
            let uu____65402 =
              let uu____65409 =
                let uu____65414 =
                  let uu____65415 =
                    let uu____65420 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____65420  in
                  FStar_TypeChecker_NBETerm.embed uu____65415 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____65414  in
              [uu____65409]  in
            uu____65396 :: uu____65402  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____65389
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65438 =
            let uu____65445 =
              let uu____65450 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65450  in
            [uu____65445]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____65438
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65460 =
            let uu____65467 =
              let uu____65472 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65472  in
            [uu____65467]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____65460
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65483 =
            let uu____65490 =
              let uu____65495 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65495  in
            let uu____65496 =
              let uu____65503 =
                let uu____65508 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____65508  in
              [uu____65503]  in
            uu____65490 :: uu____65496  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____65483
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____65538)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____65555 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____65555
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _65562  -> FStar_Pervasives_Native.Some _65562)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____65565)::(f,uu____65567)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____65588 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____65588
            (fun f1  ->
               let uu____65594 =
                 let uu____65599 =
                   let uu____65604 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____65604  in
                 FStar_TypeChecker_NBETerm.unembed uu____65599 cb ps  in
               FStar_Util.bind_opt uu____65594
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _65617  -> FStar_Pervasives_Native.Some _65617)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65622)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____65639 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65639
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65646  -> FStar_Pervasives_Native.Some _65646)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65649)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____65666 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65666
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65673  -> FStar_Pervasives_Native.Some _65673)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____65676)::(bv,uu____65678)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____65699 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65699
            (fun bv1  ->
               let uu____65705 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____65705
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _65712  -> FStar_Pervasives_Native.Some _65712)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____65713 ->
          ((let uu____65715 =
              let uu____65721 =
                let uu____65723 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____65723
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65721)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____65715);
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
    let uu____65764 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____65764
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____65795 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____65795 e_aqualv
  
let rec unlazy_as_t :
  'Auu____65805 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____65805
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____65818;
             FStar_Syntax_Syntax.rng = uu____65819;_},uu____65820)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____65839 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____65877 =
            let uu____65884 =
              let uu____65889 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65889  in
            [uu____65884]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____65877
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____65899 =
            let uu____65906 =
              let uu____65911 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65911  in
            [uu____65906]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____65899
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____65921 =
            let uu____65928 =
              let uu____65933 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65933  in
            [uu____65928]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____65921
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____65944 =
            let uu____65951 =
              let uu____65956 =
                let uu____65957 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____65957 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____65956  in
            let uu____65960 =
              let uu____65967 =
                let uu____65972 =
                  let uu____65973 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____65973 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____65972  in
              [uu____65967]  in
            uu____65951 :: uu____65960  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____65944
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____65998 =
            let uu____66005 =
              let uu____66010 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66010  in
            let uu____66011 =
              let uu____66018 =
                let uu____66023 =
                  let uu____66024 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66024 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66023  in
              [uu____66018]  in
            uu____66005 :: uu____66011  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____65998
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66041 =
            let uu____66048 =
              let uu____66053 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66053  in
            let uu____66054 =
              let uu____66061 =
                let uu____66066 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66066  in
              [uu____66061]  in
            uu____66048 :: uu____66054  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____66041
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66080 =
            let uu____66087 =
              let uu____66092 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66092  in
            [uu____66087]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____66080
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____66103 =
            let uu____66110 =
              let uu____66115 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66115  in
            let uu____66116 =
              let uu____66123 =
                let uu____66128 =
                  let uu____66129 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66129 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66128  in
              [uu____66123]  in
            uu____66110 :: uu____66116  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____66103
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66145 =
            let uu____66152 =
              let uu____66157 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66157  in
            [uu____66152]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____66145
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66168 =
            let uu____66175 =
              let uu____66180 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66180  in
            let uu____66181 =
              let uu____66188 =
                let uu____66193 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66193  in
              [uu____66188]  in
            uu____66175 :: uu____66181  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____66168
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66216 =
            let uu____66223 =
              let uu____66228 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66228  in
            let uu____66230 =
              let uu____66237 =
                let uu____66242 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66242  in
              let uu____66243 =
                let uu____66250 =
                  let uu____66255 =
                    let uu____66256 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____66256 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66255  in
                let uu____66259 =
                  let uu____66266 =
                    let uu____66271 =
                      let uu____66272 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____66272 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____66271  in
                  [uu____66266]  in
                uu____66250 :: uu____66259  in
              uu____66237 :: uu____66243  in
            uu____66223 :: uu____66230  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____66216
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____66301 =
            let uu____66308 =
              let uu____66313 =
                let uu____66314 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66314 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____66313  in
            let uu____66317 =
              let uu____66324 =
                let uu____66329 =
                  let uu____66330 =
                    let uu____66339 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____66339  in
                  FStar_TypeChecker_NBETerm.embed uu____66330 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____66329  in
              [uu____66324]  in
            uu____66308 :: uu____66317  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____66301
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____66375 =
            let uu____66382 =
              let uu____66387 =
                let uu____66388 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66388 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66387  in
            let uu____66391 =
              let uu____66398 =
                let uu____66403 =
                  let uu____66404 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66404 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66403  in
              let uu____66407 =
                let uu____66414 =
                  let uu____66419 =
                    let uu____66420 =
                      let uu____66425 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66425  in
                    FStar_TypeChecker_NBETerm.embed uu____66420 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66419  in
                [uu____66414]  in
              uu____66398 :: uu____66407  in
            uu____66382 :: uu____66391  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66375
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____66453 =
            let uu____66460 =
              let uu____66465 =
                let uu____66466 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66466 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66465  in
            let uu____66469 =
              let uu____66476 =
                let uu____66481 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66481  in
              let uu____66482 =
                let uu____66489 =
                  let uu____66494 =
                    let uu____66495 =
                      let uu____66500 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66500  in
                    FStar_TypeChecker_NBETerm.embed uu____66495 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66494  in
                [uu____66489]  in
              uu____66476 :: uu____66482  in
            uu____66460 :: uu____66469  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66453
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66541,(b,uu____66543)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____66562 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66562
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66569  -> FStar_Pervasives_Native.Some _66569)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66571,(b,uu____66573)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____66592 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66592
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66599  -> FStar_Pervasives_Native.Some _66599)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66601,(f,uu____66603)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____66622 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____66622
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _66629  -> FStar_Pervasives_Native.Some _66629)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66631,(r,uu____66633)::(l,uu____66635)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____66658 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____66658
            (fun l1  ->
               let uu____66664 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____66664
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _66671  -> FStar_Pervasives_Native.Some _66671)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66673,(t1,uu____66675)::(b,uu____66677)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____66700 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66700
            (fun b1  ->
               let uu____66706 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66706
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66713  -> FStar_Pervasives_Native.Some _66713)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66715,(t1,uu____66717)::(b,uu____66719)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____66742 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66742
            (fun b1  ->
               let uu____66748 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____66748
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _66755  -> FStar_Pervasives_Native.Some _66755)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66757,(u,uu____66759)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____66778 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____66778
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _66785  -> FStar_Pervasives_Native.Some _66785)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66787,(t1,uu____66789)::(b,uu____66791)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____66814 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66814
            (fun b1  ->
               let uu____66820 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66820
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66827  -> FStar_Pervasives_Native.Some _66827)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66829,(c,uu____66831)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____66850 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____66850
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _66857  -> FStar_Pervasives_Native.Some _66857)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66859,(l,uu____66861)::(u,uu____66863)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____66886 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____66886
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _66895  -> FStar_Pervasives_Native.Some _66895)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66897,(t2,uu____66899)::(t1,uu____66901)::(b,uu____66903)::
           (r,uu____66905)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____66936 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____66936
            (fun r1  ->
               let uu____66946 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____66946
                 (fun b1  ->
                    let uu____66952 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____66952
                      (fun t11  ->
                         let uu____66958 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____66958
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _66965  ->
                                   FStar_Pervasives_Native.Some _66965)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66968,(brs,uu____66970)::(t1,uu____66972)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____66995 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____66995
            (fun t2  ->
               let uu____67001 =
                 let uu____67006 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____67006 cb brs  in
               FStar_Util.bind_opt uu____67001
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _67021  -> FStar_Pervasives_Native.Some _67021)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67025,(tacopt,uu____67027)::(t1,uu____67029)::(e,uu____67031)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____67058 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67058
            (fun e1  ->
               let uu____67064 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____67064
                 (fun t2  ->
                    let uu____67070 =
                      let uu____67075 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67075 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67070
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67090  ->
                              FStar_Pervasives_Native.Some _67090)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67094,(tacopt,uu____67096)::(c,uu____67098)::(e,uu____67100)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____67127 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67127
            (fun e1  ->
               let uu____67133 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____67133
                 (fun c1  ->
                    let uu____67139 =
                      let uu____67144 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67144 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67139
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67159  ->
                              FStar_Pervasives_Native.Some _67159)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____67163,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _67180  -> FStar_Pervasives_Native.Some _67180)
            FStar_Reflection_Data.Tv_Unknown
      | uu____67181 ->
          ((let uu____67183 =
              let uu____67189 =
                let uu____67191 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____67191
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____67189)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____67183);
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
    let uu____67218 =
      let uu____67225 =
        let uu____67230 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____67230  in
      let uu____67232 =
        let uu____67239 =
          let uu____67244 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____67244  in
        let uu____67245 =
          let uu____67252 =
            let uu____67257 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67257  in
          [uu____67252]  in
        uu____67239 :: uu____67245  in
      uu____67225 :: uu____67232  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____67218
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67290,(s,uu____67292)::(idx,uu____67294)::(nm,uu____67296)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____67323 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____67323
          (fun nm1  ->
             let uu____67333 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____67333
               (fun idx1  ->
                  let uu____67339 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____67339
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _67346  -> FStar_Pervasives_Native.Some _67346)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____67347 ->
        ((let uu____67349 =
            let uu____67355 =
              let uu____67357 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____67357
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67355)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67349);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____67381 =
          let uu____67388 =
            let uu____67393 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____67393  in
          let uu____67394 =
            let uu____67401 =
              let uu____67406 =
                let uu____67407 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____67407 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____67406  in
            [uu____67401]  in
          uu____67388 :: uu____67394  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____67381
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____67431 =
          let uu____67438 =
            let uu____67443 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67443  in
          let uu____67444 =
            let uu____67451 =
              let uu____67456 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____67456  in
            [uu____67451]  in
          uu____67438 :: uu____67444  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____67431
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67489,(md,uu____67491)::(t1,uu____67493)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____67516 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____67516
          (fun t2  ->
             let uu____67522 =
               let uu____67527 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____67527 cb md  in
             FStar_Util.bind_opt uu____67522
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _67542  -> FStar_Pervasives_Native.Some _67542)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67546,(post,uu____67548)::(pre,uu____67550)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____67573 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____67573
          (fun pre1  ->
             let uu____67579 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____67579
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _67586  -> FStar_Pervasives_Native.Some _67586)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67588,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _67605  -> FStar_Pervasives_Native.Some _67605)
          FStar_Reflection_Data.C_Unknown
    | uu____67606 ->
        ((let uu____67608 =
            let uu____67614 =
              let uu____67616 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____67616
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67614)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67608);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67662,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67678,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67694,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____67709 ->
        ((let uu____67711 =
            let uu____67717 =
              let uu____67719 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____67719  in
            (FStar_Errors.Warning_NotEmbedded, uu____67717)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67711);
         FStar_Pervasives_Native.None)
     in
  let uu____67723 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____67723 
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
           FStar_Syntax_Syntax.ltyp = uu____67754;
           FStar_Syntax_Syntax.rng = uu____67755;_},uu____67756)
        ->
        let uu____67775 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____67775
    | uu____67776 ->
        ((let uu____67778 =
            let uu____67784 =
              let uu____67786 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____67786  in
            (FStar_Errors.Warning_NotEmbedded, uu____67784)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67778);
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
    let uu____67815 =
      let uu____67821 = FStar_Ident.range_of_id i  in
      let uu____67822 = FStar_Ident.text_of_id i  in
      (uu____67821, uu____67822)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____67815  in
  let unembed_ident cb t =
    let uu____67845 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____67845 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____67869 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____67869
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
    let uu____67879 =
      let uu____67887 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____67889 =
        let uu____67892 = fv_as_emb_typ range_fv  in
        let uu____67893 =
          let uu____67896 = fv_as_emb_typ string_fv  in [uu____67896]  in
        uu____67892 :: uu____67893  in
      (uu____67887, uu____67889)  in
    FStar_Syntax_Syntax.ET_app uu____67879  in
  let uu____67900 =
    let uu____67901 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____67902 =
      let uu____67909 =
        let uu____67914 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____67914  in
      let uu____67919 =
        let uu____67926 =
          let uu____67931 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____67931  in
        [uu____67926]  in
      uu____67909 :: uu____67919  in
    mkFV uu____67901 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____67902
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____67900 et 
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
        let uu____67988 =
          let uu____67995 =
            let uu____68000 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____68000  in
          let uu____68002 =
            let uu____68009 =
              let uu____68014 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68014  in
            let uu____68015 =
              let uu____68022 =
                let uu____68027 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____68027  in
              let uu____68030 =
                let uu____68037 =
                  let uu____68042 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68042  in
                let uu____68043 =
                  let uu____68050 =
                    let uu____68055 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68055  in
                  [uu____68050]  in
                uu____68037 :: uu____68043  in
              uu____68022 :: uu____68030  in
            uu____68009 :: uu____68015  in
          uu____67995 :: uu____68002  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____67988
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____68082 =
          let uu____68089 =
            let uu____68094 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68094  in
          let uu____68098 =
            let uu____68105 =
              let uu____68110 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68110  in
            [uu____68105]  in
          uu____68089 :: uu____68098  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____68082
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____68140 =
          let uu____68147 =
            let uu____68152 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68152  in
          let uu____68156 =
            let uu____68163 =
              let uu____68168 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____68168  in
            let uu____68171 =
              let uu____68178 =
                let uu____68183 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____68183  in
              let uu____68184 =
                let uu____68191 =
                  let uu____68196 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68196  in
                let uu____68197 =
                  let uu____68204 =
                    let uu____68209 =
                      let uu____68210 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____68210 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68209  in
                  [uu____68204]  in
                uu____68191 :: uu____68197  in
              uu____68178 :: uu____68184  in
            uu____68163 :: uu____68171  in
          uu____68147 :: uu____68156  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____68140
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68270,(dcs,uu____68272)::(t1,uu____68274)::(bs,uu____68276)::
         (us,uu____68278)::(nm,uu____68280)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____68315 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____68315
          (fun nm1  ->
             let uu____68333 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____68333
               (fun us1  ->
                  let uu____68347 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____68347
                    (fun bs1  ->
                       let uu____68353 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____68353
                         (fun t2  ->
                            let uu____68359 =
                              let uu____68367 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____68367
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____68359
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _68397  ->
                                      FStar_Pervasives_Native.Some _68397)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68405,(t1,uu____68407)::(ty,uu____68409)::(univs1,uu____68411)::
         (fvar1,uu____68413)::(r,uu____68415)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____68450 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____68450
          (fun r1  ->
             let uu____68460 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____68460
               (fun fvar2  ->
                  let uu____68466 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____68466
                    (fun univs2  ->
                       let uu____68480 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____68480
                         (fun ty1  ->
                            let uu____68486 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____68486
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _68493  ->
                                      FStar_Pervasives_Native.Some _68493)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68498,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____68513 ->
        ((let uu____68515 =
            let uu____68521 =
              let uu____68523 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____68523
               in
            (FStar_Errors.Warning_NotEmbedded, uu____68521)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68515);
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
        let uu____68546 =
          let uu____68553 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____68553]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____68546
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____68568 =
          let uu____68575 =
            let uu____68580 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____68580  in
          let uu____68581 =
            let uu____68588 =
              let uu____68593 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____68593  in
            [uu____68588]  in
          uu____68575 :: uu____68581  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____68568
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68622,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68638,(i,uu____68640)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____68659 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____68659
          (fun i1  ->
             FStar_All.pipe_left
               (fun _68666  -> FStar_Pervasives_Native.Some _68666)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68668,(e2,uu____68670)::(e1,uu____68672)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____68695 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____68695
          (fun e11  ->
             let uu____68701 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____68701
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _68708  -> FStar_Pervasives_Native.Some _68708)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____68709 ->
        ((let uu____68711 =
            let uu____68717 =
              let uu____68719 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____68719  in
            (FStar_Errors.Warning_NotEmbedded, uu____68717)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68711);
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