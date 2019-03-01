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
    let uu____64310 =
      let uu____64318 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____64318, [])  in
    FStar_Syntax_Syntax.ET_app uu____64310
  
let mk_emb' :
  'Auu____64332 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____64332 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____64332 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____64332 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____64374 = mkFV fv [] []  in
        let uu____64379 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____64374 uu____64379
  
let mk_lazy :
  'Auu____64391 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____64391 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____64417 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____64417;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____64423  ->
                 let uu____64424 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____64424)
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
           FStar_Syntax_Syntax.ltyp = uu____64509;
           FStar_Syntax_Syntax.rng = uu____64510;_},uu____64511)
        ->
        let uu____64530 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _64533  -> FStar_Pervasives_Native.Some _64533) uu____64530
    | uu____64534 ->
        ((let uu____64536 =
            let uu____64542 =
              let uu____64544 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____64544  in
            (FStar_Errors.Warning_NotEmbedded, uu____64542)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64536);
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
           FStar_Syntax_Syntax.ltyp = uu____64578;
           FStar_Syntax_Syntax.rng = uu____64579;_},uu____64580)
        ->
        let uu____64599 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64599
    | uu____64600 ->
        ((let uu____64602 =
            let uu____64608 =
              let uu____64610 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____64610  in
            (FStar_Errors.Warning_NotEmbedded, uu____64608)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64602);
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
          let uu____64660 = f x  in
          FStar_Util.bind_opt uu____64660
            (fun x1  ->
               let uu____64668 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____64668
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
      | uu____64738 -> FStar_Pervasives_Native.None  in
    let uu____64739 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____64744 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____64739;
      FStar_TypeChecker_NBETerm.emb_typ = uu____64744
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
        let uu____64777 =
          let uu____64784 =
            let uu____64789 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____64789  in
          [uu____64784]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____64777
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____64841)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____64858 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____64858
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____64863 ->
        ((let uu____64865 =
            let uu____64871 =
              let uu____64873 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____64873  in
            (FStar_Errors.Warning_NotEmbedded, uu____64871)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64865);
         FStar_Pervasives_Native.None)
     in
  let uu____64877 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____64882 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____64877
    uu____64882
  
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
           FStar_Syntax_Syntax.ltyp = uu____64916;
           FStar_Syntax_Syntax.rng = uu____64917;_},uu____64918)
        ->
        let uu____64937 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64937
    | uu____64938 ->
        ((let uu____64940 =
            let uu____64946 =
              let uu____64948 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____64948  in
            (FStar_Errors.Warning_NotEmbedded, uu____64946)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64940);
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
           FStar_Syntax_Syntax.ltyp = uu____64982;
           FStar_Syntax_Syntax.rng = uu____64983;_},uu____64984)
        ->
        let uu____65003 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65003
    | uu____65004 ->
        ((let uu____65006 =
            let uu____65012 =
              let uu____65014 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____65014  in
            (FStar_Errors.Warning_NotEmbedded, uu____65012)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65006);
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
           FStar_Syntax_Syntax.ltyp = uu____65048;
           FStar_Syntax_Syntax.rng = uu____65049;_},uu____65050)
        ->
        let uu____65069 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____65069
    | uu____65070 ->
        ((let uu____65072 =
            let uu____65078 =
              let uu____65080 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____65080  in
            (FStar_Errors.Warning_NotEmbedded, uu____65078)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65072);
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
        let uu____65111 =
          let uu____65118 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____65118]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____65111
    | FStar_Reflection_Data.C_String s ->
        let uu____65133 =
          let uu____65140 =
            let uu____65145 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65145  in
          [uu____65140]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____65133
    | FStar_Reflection_Data.C_Range r ->
        let uu____65156 =
          let uu____65163 =
            let uu____65168 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65168  in
          [uu____65163]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____65156
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____65182 =
          let uu____65189 =
            let uu____65194 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____65194  in
          [uu____65189]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____65182
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____65262)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____65279 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____65279
          (fun i1  ->
             FStar_All.pipe_left
               (fun _65286  -> FStar_Pervasives_Native.Some _65286)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____65289)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____65306 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____65306
          (fun s1  ->
             FStar_All.pipe_left
               (fun _65317  -> FStar_Pervasives_Native.Some _65317)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____65320)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____65337 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____65337
          (fun r1  ->
             FStar_All.pipe_left
               (fun _65344  -> FStar_Pervasives_Native.Some _65344)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____65360)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____65377 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____65377
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _65396  -> FStar_Pervasives_Native.Some _65396)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____65397 ->
        ((let uu____65399 =
            let uu____65405 =
              let uu____65407 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____65407  in
            (FStar_Errors.Warning_NotEmbedded, uu____65405)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____65399);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____65418  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____65431 =
            let uu____65438 =
              let uu____65443 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65443  in
            [uu____65438]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____65431
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____65458 =
            let uu____65465 =
              let uu____65470 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65470  in
            let uu____65471 =
              let uu____65478 =
                let uu____65483 =
                  let uu____65484 =
                    let uu____65489 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____65489  in
                  FStar_TypeChecker_NBETerm.embed uu____65484 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____65483  in
              [uu____65478]  in
            uu____65465 :: uu____65471  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____65458
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____65507 =
            let uu____65514 =
              let uu____65519 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65519  in
            [uu____65514]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____65507
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____65529 =
            let uu____65536 =
              let uu____65541 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65541  in
            [uu____65536]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____65529
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____65552 =
            let uu____65559 =
              let uu____65564 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65564  in
            let uu____65565 =
              let uu____65572 =
                let uu____65577 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____65577  in
              [uu____65572]  in
            uu____65559 :: uu____65565  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____65552
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____65607)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____65624 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____65624
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _65631  -> FStar_Pervasives_Native.Some _65631)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____65634)::(f,uu____65636)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____65657 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____65657
            (fun f1  ->
               let uu____65663 =
                 let uu____65668 =
                   let uu____65673 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____65673  in
                 FStar_TypeChecker_NBETerm.unembed uu____65668 cb ps  in
               FStar_Util.bind_opt uu____65663
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _65686  -> FStar_Pervasives_Native.Some _65686)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65691)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____65708 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65708
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65715  -> FStar_Pervasives_Native.Some _65715)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____65718)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____65735 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65735
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _65742  -> FStar_Pervasives_Native.Some _65742)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____65745)::(bv,uu____65747)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____65768 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____65768
            (fun bv1  ->
               let uu____65774 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____65774
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _65781  -> FStar_Pervasives_Native.Some _65781)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____65782 ->
          ((let uu____65784 =
              let uu____65790 =
                let uu____65792 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____65792
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____65790)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____65784);
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
    let uu____65833 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____65833
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____65864 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____65864 e_aqualv
  
let rec unlazy_as_t :
  'Auu____65874 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____65874
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____65887;
             FStar_Syntax_Syntax.rng = uu____65888;_},uu____65889)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____65908 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____65946 =
            let uu____65953 =
              let uu____65958 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65958  in
            [uu____65953]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____65946
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____65968 =
            let uu____65975 =
              let uu____65980 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____65980  in
            [uu____65975]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____65968
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____65990 =
            let uu____65997 =
              let uu____66002 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66002  in
            [uu____65997]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____65990
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____66013 =
            let uu____66020 =
              let uu____66025 =
                let uu____66026 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66026 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____66025  in
            let uu____66029 =
              let uu____66036 =
                let uu____66041 =
                  let uu____66042 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66042 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____66041  in
              [uu____66036]  in
            uu____66020 :: uu____66029  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____66013
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____66067 =
            let uu____66074 =
              let uu____66079 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66079  in
            let uu____66080 =
              let uu____66087 =
                let uu____66092 =
                  let uu____66093 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66093 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66092  in
              [uu____66087]  in
            uu____66074 :: uu____66080  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____66067
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____66110 =
            let uu____66117 =
              let uu____66122 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66122  in
            let uu____66123 =
              let uu____66130 =
                let uu____66135 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66135  in
              [uu____66130]  in
            uu____66117 :: uu____66123  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____66110
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____66149 =
            let uu____66156 =
              let uu____66161 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66161  in
            [uu____66156]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____66149
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____66172 =
            let uu____66179 =
              let uu____66184 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66184  in
            let uu____66185 =
              let uu____66192 =
                let uu____66197 =
                  let uu____66198 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66198 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66197  in
              [uu____66192]  in
            uu____66179 :: uu____66185  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____66172
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____66214 =
            let uu____66221 =
              let uu____66226 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66226  in
            [uu____66221]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____66214
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____66237 =
            let uu____66244 =
              let uu____66249 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66249  in
            let uu____66250 =
              let uu____66257 =
                let uu____66262 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66262  in
              [uu____66257]  in
            uu____66244 :: uu____66250  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____66237
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____66285 =
            let uu____66292 =
              let uu____66297 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____66297  in
            let uu____66299 =
              let uu____66306 =
                let uu____66311 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66311  in
              let uu____66312 =
                let uu____66319 =
                  let uu____66324 =
                    let uu____66325 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____66325 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66324  in
                let uu____66328 =
                  let uu____66335 =
                    let uu____66340 =
                      let uu____66341 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____66341 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____66340  in
                  [uu____66335]  in
                uu____66319 :: uu____66328  in
              uu____66306 :: uu____66312  in
            uu____66292 :: uu____66299  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____66285
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____66370 =
            let uu____66377 =
              let uu____66382 =
                let uu____66383 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66383 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____66382  in
            let uu____66386 =
              let uu____66393 =
                let uu____66398 =
                  let uu____66399 =
                    let uu____66408 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____66408  in
                  FStar_TypeChecker_NBETerm.embed uu____66399 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____66398  in
              [uu____66393]  in
            uu____66377 :: uu____66386  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____66370
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____66444 =
            let uu____66451 =
              let uu____66456 =
                let uu____66457 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66457 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66456  in
            let uu____66460 =
              let uu____66467 =
                let uu____66472 =
                  let uu____66473 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____66473 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____66472  in
              let uu____66476 =
                let uu____66483 =
                  let uu____66488 =
                    let uu____66489 =
                      let uu____66494 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66494  in
                    FStar_TypeChecker_NBETerm.embed uu____66489 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66488  in
                [uu____66483]  in
              uu____66467 :: uu____66476  in
            uu____66451 :: uu____66460  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66444
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____66522 =
            let uu____66529 =
              let uu____66534 =
                let uu____66535 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____66535 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____66534  in
            let uu____66538 =
              let uu____66545 =
                let uu____66550 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____66550  in
              let uu____66551 =
                let uu____66558 =
                  let uu____66563 =
                    let uu____66564 =
                      let uu____66569 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____66569  in
                    FStar_TypeChecker_NBETerm.embed uu____66564 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____66563  in
                [uu____66558]  in
              uu____66545 :: uu____66551  in
            uu____66529 :: uu____66538  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____66522
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66610,(b,uu____66612)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____66631 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66631
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66638  -> FStar_Pervasives_Native.Some _66638)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66640,(b,uu____66642)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____66661 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66661
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _66668  -> FStar_Pervasives_Native.Some _66668)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66670,(f,uu____66672)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____66691 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____66691
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _66698  -> FStar_Pervasives_Native.Some _66698)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66700,(r,uu____66702)::(l,uu____66704)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____66727 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____66727
            (fun l1  ->
               let uu____66733 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____66733
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _66740  -> FStar_Pervasives_Native.Some _66740)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66742,(t1,uu____66744)::(b,uu____66746)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____66769 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66769
            (fun b1  ->
               let uu____66775 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66775
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66782  -> FStar_Pervasives_Native.Some _66782)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66784,(t1,uu____66786)::(b,uu____66788)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____66811 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____66811
            (fun b1  ->
               let uu____66817 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____66817
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _66824  -> FStar_Pervasives_Native.Some _66824)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66826,(u,uu____66828)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____66847 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____66847
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _66854  -> FStar_Pervasives_Native.Some _66854)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66856,(t1,uu____66858)::(b,uu____66860)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____66883 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____66883
            (fun b1  ->
               let uu____66889 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____66889
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _66896  -> FStar_Pervasives_Native.Some _66896)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66898,(c,uu____66900)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____66919 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____66919
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _66926  -> FStar_Pervasives_Native.Some _66926)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66928,(l,uu____66930)::(u,uu____66932)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____66955 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____66955
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _66964  -> FStar_Pervasives_Native.Some _66964)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____66966,(t2,uu____66968)::(t1,uu____66970)::(b,uu____66972)::
           (r,uu____66974)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____67005 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____67005
            (fun r1  ->
               let uu____67015 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____67015
                 (fun b1  ->
                    let uu____67021 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____67021
                      (fun t11  ->
                         let uu____67027 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____67027
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _67034  ->
                                   FStar_Pervasives_Native.Some _67034)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67037,(brs,uu____67039)::(t1,uu____67041)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____67064 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____67064
            (fun t2  ->
               let uu____67070 =
                 let uu____67075 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____67075 cb brs  in
               FStar_Util.bind_opt uu____67070
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _67090  -> FStar_Pervasives_Native.Some _67090)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67094,(tacopt,uu____67096)::(t1,uu____67098)::(e,uu____67100)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____67127 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67127
            (fun e1  ->
               let uu____67133 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____67133
                 (fun t2  ->
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
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____67163,(tacopt,uu____67165)::(c,uu____67167)::(e,uu____67169)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____67196 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____67196
            (fun e1  ->
               let uu____67202 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____67202
                 (fun c1  ->
                    let uu____67208 =
                      let uu____67213 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____67213 cb tacopt
                       in
                    FStar_Util.bind_opt uu____67208
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _67228  ->
                              FStar_Pervasives_Native.Some _67228)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____67232,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _67249  -> FStar_Pervasives_Native.Some _67249)
            FStar_Reflection_Data.Tv_Unknown
      | uu____67250 ->
          ((let uu____67252 =
              let uu____67258 =
                let uu____67260 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____67260
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____67258)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____67252);
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
    let uu____67287 =
      let uu____67294 =
        let uu____67299 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____67299  in
      let uu____67301 =
        let uu____67308 =
          let uu____67313 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____67313  in
        let uu____67314 =
          let uu____67321 =
            let uu____67326 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67326  in
          [uu____67321]  in
        uu____67308 :: uu____67314  in
      uu____67294 :: uu____67301  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____67287
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67359,(s,uu____67361)::(idx,uu____67363)::(nm,uu____67365)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____67392 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____67392
          (fun nm1  ->
             let uu____67402 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____67402
               (fun idx1  ->
                  let uu____67408 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____67408
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _67415  -> FStar_Pervasives_Native.Some _67415)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____67416 ->
        ((let uu____67418 =
            let uu____67424 =
              let uu____67426 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____67426
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67424)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67418);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____67450 =
          let uu____67457 =
            let uu____67462 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____67462  in
          let uu____67463 =
            let uu____67470 =
              let uu____67475 =
                let uu____67476 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____67476 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____67475  in
            [uu____67470]  in
          uu____67457 :: uu____67463  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____67450
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____67500 =
          let uu____67507 =
            let uu____67512 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____67512  in
          let uu____67513 =
            let uu____67520 =
              let uu____67525 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____67525  in
            [uu____67520]  in
          uu____67507 :: uu____67513  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____67500
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67558,(md,uu____67560)::(t1,uu____67562)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____67585 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____67585
          (fun t2  ->
             let uu____67591 =
               let uu____67596 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____67596 cb md  in
             FStar_Util.bind_opt uu____67591
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _67611  -> FStar_Pervasives_Native.Some _67611)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____67615,(post,uu____67617)::(pre,uu____67619)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____67642 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____67642
          (fun pre1  ->
             let uu____67648 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____67648
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _67655  -> FStar_Pervasives_Native.Some _67655)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67657,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _67674  -> FStar_Pervasives_Native.Some _67674)
          FStar_Reflection_Data.C_Unknown
    | uu____67675 ->
        ((let uu____67677 =
            let uu____67683 =
              let uu____67685 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____67685
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67683)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67677);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67731,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67747,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____67763,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____67778 ->
        ((let uu____67780 =
            let uu____67786 =
              let uu____67788 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____67788  in
            (FStar_Errors.Warning_NotEmbedded, uu____67786)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67780);
         FStar_Pervasives_Native.None)
     in
  let uu____67792 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____67792 
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
           FStar_Syntax_Syntax.ltyp = uu____67823;
           FStar_Syntax_Syntax.rng = uu____67824;_},uu____67825)
        ->
        let uu____67844 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____67844
    | uu____67845 ->
        ((let uu____67847 =
            let uu____67853 =
              let uu____67855 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____67855  in
            (FStar_Errors.Warning_NotEmbedded, uu____67853)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67847);
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
    let uu____67884 =
      let uu____67890 = FStar_Ident.range_of_id i  in
      let uu____67891 = FStar_Ident.text_of_id i  in
      (uu____67890, uu____67891)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____67884  in
  let unembed_ident cb t =
    let uu____67914 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____67914 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____67938 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____67938
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
    let uu____67948 =
      let uu____67956 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____67958 =
        let uu____67961 = fv_as_emb_typ range_fv  in
        let uu____67962 =
          let uu____67965 = fv_as_emb_typ string_fv  in [uu____67965]  in
        uu____67961 :: uu____67962  in
      (uu____67956, uu____67958)  in
    FStar_Syntax_Syntax.ET_app uu____67948  in
  let uu____67969 =
    let uu____67970 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____67971 =
      let uu____67978 =
        let uu____67983 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____67983  in
      let uu____67988 =
        let uu____67995 =
          let uu____68000 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____68000  in
        [uu____67995]  in
      uu____67978 :: uu____67988  in
    mkFV uu____67970 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____67971
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____67969 et 
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
        let uu____68057 =
          let uu____68064 =
            let uu____68069 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____68069  in
          let uu____68071 =
            let uu____68078 =
              let uu____68083 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68083  in
            let uu____68084 =
              let uu____68091 =
                let uu____68096 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____68096  in
              let uu____68099 =
                let uu____68106 =
                  let uu____68111 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68111  in
                let uu____68112 =
                  let uu____68119 =
                    let uu____68124 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68124  in
                  [uu____68119]  in
                uu____68106 :: uu____68112  in
              uu____68091 :: uu____68099  in
            uu____68078 :: uu____68084  in
          uu____68064 :: uu____68071  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____68057
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____68151 =
          let uu____68158 =
            let uu____68163 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68163  in
          let uu____68167 =
            let uu____68174 =
              let uu____68179 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____68179  in
            [uu____68174]  in
          uu____68158 :: uu____68167  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____68151
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____68209 =
          let uu____68216 =
            let uu____68221 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____68221  in
          let uu____68225 =
            let uu____68232 =
              let uu____68237 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____68237  in
            let uu____68240 =
              let uu____68247 =
                let uu____68252 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____68252  in
              let uu____68253 =
                let uu____68260 =
                  let uu____68265 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____68265  in
                let uu____68266 =
                  let uu____68273 =
                    let uu____68278 =
                      let uu____68279 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____68279 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____68278  in
                  [uu____68273]  in
                uu____68260 :: uu____68266  in
              uu____68247 :: uu____68253  in
            uu____68232 :: uu____68240  in
          uu____68216 :: uu____68225  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____68209
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68339,(dcs,uu____68341)::(t1,uu____68343)::(bs,uu____68345)::
         (us,uu____68347)::(nm,uu____68349)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____68384 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____68384
          (fun nm1  ->
             let uu____68402 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____68402
               (fun us1  ->
                  let uu____68416 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____68416
                    (fun bs1  ->
                       let uu____68422 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____68422
                         (fun t2  ->
                            let uu____68428 =
                              let uu____68436 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____68436
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____68428
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _68466  ->
                                      FStar_Pervasives_Native.Some _68466)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68474,(t1,uu____68476)::(ty,uu____68478)::(univs1,uu____68480)::
         (fvar1,uu____68482)::(r,uu____68484)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____68519 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____68519
          (fun r1  ->
             let uu____68529 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____68529
               (fun fvar2  ->
                  let uu____68535 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____68535
                    (fun univs2  ->
                       let uu____68549 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____68549
                         (fun ty1  ->
                            let uu____68555 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____68555
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _68562  ->
                                      FStar_Pervasives_Native.Some _68562)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68567,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____68582 ->
        ((let uu____68584 =
            let uu____68590 =
              let uu____68592 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____68592
               in
            (FStar_Errors.Warning_NotEmbedded, uu____68590)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68584);
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
        let uu____68615 =
          let uu____68622 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____68622]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____68615
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____68637 =
          let uu____68644 =
            let uu____68649 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____68649  in
          let uu____68650 =
            let uu____68657 =
              let uu____68662 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____68662  in
            [uu____68657]  in
          uu____68644 :: uu____68650  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____68637
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____68691,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68707,(i,uu____68709)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____68728 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____68728
          (fun i1  ->
             FStar_All.pipe_left
               (fun _68735  -> FStar_Pervasives_Native.Some _68735)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____68737,(e2,uu____68739)::(e1,uu____68741)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____68764 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____68764
          (fun e11  ->
             let uu____68770 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____68770
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _68777  -> FStar_Pervasives_Native.Some _68777)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____68778 ->
        ((let uu____68780 =
            let uu____68786 =
              let uu____68788 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____68788  in
            (FStar_Errors.Warning_NotEmbedded, uu____68786)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____68780);
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