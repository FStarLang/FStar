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
    let uu____59456 =
      let uu____59464 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____59464, [])  in
    FStar_Syntax_Syntax.ET_app uu____59456
  
let mk_emb' :
  'Auu____59478 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____59478 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____59478 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____59478 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____59520 = mkFV fv [] []  in
        let uu____59525 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____59520 uu____59525
  
let mk_lazy :
  'Auu____59537 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____59537 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____59563 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____59563;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____59569  ->
                 let uu____59570 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____59570)
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
           FStar_Syntax_Syntax.ltyp = uu____59615;
           FStar_Syntax_Syntax.rng = uu____59616;_},uu____59617)
        ->
        let uu____59636 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _59639  -> FStar_Pervasives_Native.Some _59639) uu____59636
    | uu____59640 ->
        ((let uu____59642 =
            let uu____59648 =
              let uu____59650 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____59650  in
            (FStar_Errors.Warning_NotEmbedded, uu____59648)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59642);
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
           FStar_Syntax_Syntax.ltyp = uu____59684;
           FStar_Syntax_Syntax.rng = uu____59685;_},uu____59686)
        ->
        let uu____59705 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59705
    | uu____59706 ->
        ((let uu____59708 =
            let uu____59714 =
              let uu____59716 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____59716  in
            (FStar_Errors.Warning_NotEmbedded, uu____59714)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59708);
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
          let uu____59766 = f x  in
          FStar_Util.bind_opt uu____59766
            (fun x1  ->
               let uu____59774 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59774
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
      | uu____59844 -> FStar_Pervasives_Native.None  in
    let uu____59845 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____59850 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____59845;
      FStar_TypeChecker_NBETerm.emb_typ = uu____59850
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
        let uu____59883 =
          let uu____59890 =
            let uu____59895 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____59895  in
          [uu____59890]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____59883
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____59947)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____59964 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____59964
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____59969 ->
        ((let uu____59971 =
            let uu____59977 =
              let uu____59979 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____59979  in
            (FStar_Errors.Warning_NotEmbedded, uu____59977)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59971);
         FStar_Pervasives_Native.None)
     in
  let uu____59983 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____59988 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____59983
    uu____59988
  
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
           FStar_Syntax_Syntax.ltyp = uu____60022;
           FStar_Syntax_Syntax.rng = uu____60023;_},uu____60024)
        ->
        let uu____60043 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60043
    | uu____60044 ->
        ((let uu____60046 =
            let uu____60052 =
              let uu____60054 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____60054  in
            (FStar_Errors.Warning_NotEmbedded, uu____60052)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60046);
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
           FStar_Syntax_Syntax.ltyp = uu____60088;
           FStar_Syntax_Syntax.rng = uu____60089;_},uu____60090)
        ->
        let uu____60109 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60109
    | uu____60110 ->
        ((let uu____60112 =
            let uu____60118 =
              let uu____60120 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____60120  in
            (FStar_Errors.Warning_NotEmbedded, uu____60118)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60112);
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
           FStar_Syntax_Syntax.ltyp = uu____60154;
           FStar_Syntax_Syntax.rng = uu____60155;_},uu____60156)
        ->
        let uu____60175 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60175
    | uu____60176 ->
        ((let uu____60178 =
            let uu____60184 =
              let uu____60186 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____60186  in
            (FStar_Errors.Warning_NotEmbedded, uu____60184)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60178);
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
        let uu____60217 =
          let uu____60224 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____60224]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____60217
    | FStar_Reflection_Data.C_String s ->
        let uu____60239 =
          let uu____60246 =
            let uu____60251 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60251  in
          [uu____60246]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____60239
    | FStar_Reflection_Data.C_Range r ->
        let uu____60262 =
          let uu____60269 =
            let uu____60274 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60274  in
          [uu____60269]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____60262
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____60288 =
          let uu____60295 =
            let uu____60300 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60300  in
          [uu____60295]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____60288
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____60368)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____60385 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____60385
          (fun i1  ->
             FStar_All.pipe_left
               (fun _60392  -> FStar_Pervasives_Native.Some _60392)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____60395)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____60412 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____60412
          (fun s1  ->
             FStar_All.pipe_left
               (fun _60423  -> FStar_Pervasives_Native.Some _60423)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____60426)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____60443 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____60443
          (fun r1  ->
             FStar_All.pipe_left
               (fun _60450  -> FStar_Pervasives_Native.Some _60450)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____60466)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____60483 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____60483
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _60502  -> FStar_Pervasives_Native.Some _60502)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____60503 ->
        ((let uu____60505 =
            let uu____60511 =
              let uu____60513 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____60513  in
            (FStar_Errors.Warning_NotEmbedded, uu____60511)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60505);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____60524  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60537 =
            let uu____60544 =
              let uu____60549 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60549  in
            [uu____60544]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____60537
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60564 =
            let uu____60571 =
              let uu____60576 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60576  in
            let uu____60577 =
              let uu____60584 =
                let uu____60589 =
                  let uu____60590 =
                    let uu____60595 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____60595  in
                  FStar_TypeChecker_NBETerm.embed uu____60590 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____60589  in
              [uu____60584]  in
            uu____60571 :: uu____60577  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____60564
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60613 =
            let uu____60620 =
              let uu____60625 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60625  in
            [uu____60620]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____60613
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____60635 =
            let uu____60642 =
              let uu____60647 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60647  in
            [uu____60642]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____60635
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____60658 =
            let uu____60665 =
              let uu____60670 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60670  in
            let uu____60671 =
              let uu____60678 =
                let uu____60683 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____60683  in
              [uu____60678]  in
            uu____60665 :: uu____60671  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____60658
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____60713)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____60730 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____60730
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _60737  -> FStar_Pervasives_Native.Some _60737)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____60740)::(f,uu____60742)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____60763 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____60763
            (fun f1  ->
               let uu____60769 =
                 let uu____60774 =
                   let uu____60779 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____60779  in
                 FStar_TypeChecker_NBETerm.unembed uu____60774 cb ps  in
               FStar_Util.bind_opt uu____60769
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _60792  -> FStar_Pervasives_Native.Some _60792)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60797)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____60814 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60814
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60821  -> FStar_Pervasives_Native.Some _60821)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60824)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____60841 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60841
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60848  -> FStar_Pervasives_Native.Some _60848)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____60851)::(bv,uu____60853)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____60874 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60874
            (fun bv1  ->
               let uu____60880 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____60880
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _60887  -> FStar_Pervasives_Native.Some _60887)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____60888 ->
          ((let uu____60890 =
              let uu____60896 =
                let uu____60898 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____60898
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____60896)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____60890);
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
    let uu____60939 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____60939
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____60970 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____60970 e_aqualv
  
let rec unlazy_as_t :
  'Auu____60980 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____60980
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____60993;
             FStar_Syntax_Syntax.rng = uu____60994;_},uu____60995)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____61014 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61052 =
            let uu____61059 =
              let uu____61064 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61064  in
            [uu____61059]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____61052
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____61074 =
            let uu____61081 =
              let uu____61086 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61086  in
            [uu____61081]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____61074
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61096 =
            let uu____61103 =
              let uu____61108 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61108  in
            [uu____61103]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____61096
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61119 =
            let uu____61126 =
              let uu____61131 =
                let uu____61132 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61132 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____61131  in
            let uu____61135 =
              let uu____61142 =
                let uu____61147 =
                  let uu____61148 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61148 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____61147  in
              [uu____61142]  in
            uu____61126 :: uu____61135  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____61119
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____61173 =
            let uu____61180 =
              let uu____61185 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61185  in
            let uu____61186 =
              let uu____61193 =
                let uu____61198 =
                  let uu____61199 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61199 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61198  in
              [uu____61193]  in
            uu____61180 :: uu____61186  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____61173
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61216 =
            let uu____61223 =
              let uu____61228 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61228  in
            let uu____61229 =
              let uu____61236 =
                let uu____61241 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61241  in
              [uu____61236]  in
            uu____61223 :: uu____61229  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____61216
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61255 =
            let uu____61262 =
              let uu____61267 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61267  in
            [uu____61262]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____61255
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____61278 =
            let uu____61285 =
              let uu____61290 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61290  in
            let uu____61291 =
              let uu____61298 =
                let uu____61303 =
                  let uu____61304 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61304 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61303  in
              [uu____61298]  in
            uu____61285 :: uu____61291  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____61278
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61320 =
            let uu____61327 =
              let uu____61332 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61332  in
            [uu____61327]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____61320
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61343 =
            let uu____61350 =
              let uu____61355 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61355  in
            let uu____61356 =
              let uu____61363 =
                let uu____61368 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61368  in
              [uu____61363]  in
            uu____61350 :: uu____61356  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____61343
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____61391 =
            let uu____61398 =
              let uu____61403 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61403  in
            let uu____61405 =
              let uu____61412 =
                let uu____61417 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61417  in
              let uu____61418 =
                let uu____61425 =
                  let uu____61430 =
                    let uu____61431 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____61431 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61430  in
                let uu____61434 =
                  let uu____61441 =
                    let uu____61446 =
                      let uu____61447 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____61447 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____61446  in
                  [uu____61441]  in
                uu____61425 :: uu____61434  in
              uu____61412 :: uu____61418  in
            uu____61398 :: uu____61405  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____61391
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____61476 =
            let uu____61483 =
              let uu____61488 =
                let uu____61489 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61489 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____61488  in
            let uu____61492 =
              let uu____61499 =
                let uu____61504 =
                  let uu____61505 =
                    let uu____61514 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____61514  in
                  FStar_TypeChecker_NBETerm.embed uu____61505 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____61504  in
              [uu____61499]  in
            uu____61483 :: uu____61492  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____61476
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____61550 =
            let uu____61557 =
              let uu____61562 =
                let uu____61563 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61563 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61562  in
            let uu____61566 =
              let uu____61573 =
                let uu____61578 =
                  let uu____61579 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61579 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61578  in
              let uu____61582 =
                let uu____61589 =
                  let uu____61594 =
                    let uu____61595 =
                      let uu____61600 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61600  in
                    FStar_TypeChecker_NBETerm.embed uu____61595 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61594  in
                [uu____61589]  in
              uu____61573 :: uu____61582  in
            uu____61557 :: uu____61566  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61550
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____61628 =
            let uu____61635 =
              let uu____61640 =
                let uu____61641 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61641 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61640  in
            let uu____61644 =
              let uu____61651 =
                let uu____61656 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61656  in
              let uu____61657 =
                let uu____61664 =
                  let uu____61669 =
                    let uu____61670 =
                      let uu____61675 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61675  in
                    FStar_TypeChecker_NBETerm.embed uu____61670 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61669  in
                [uu____61664]  in
              uu____61651 :: uu____61657  in
            uu____61635 :: uu____61644  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61628
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61716,(b,uu____61718)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____61737 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61737
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61744  -> FStar_Pervasives_Native.Some _61744)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61746,(b,uu____61748)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____61767 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61767
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61774  -> FStar_Pervasives_Native.Some _61774)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61776,(f,uu____61778)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____61797 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____61797
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _61804  -> FStar_Pervasives_Native.Some _61804)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61806,(r,uu____61808)::(l,uu____61810)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____61833 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____61833
            (fun l1  ->
               let uu____61839 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____61839
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _61846  -> FStar_Pervasives_Native.Some _61846)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61848,(t1,uu____61850)::(b,uu____61852)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____61875 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61875
            (fun b1  ->
               let uu____61881 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61881
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _61888  -> FStar_Pervasives_Native.Some _61888)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61890,(t1,uu____61892)::(b,uu____61894)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____61917 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61917
            (fun b1  ->
               let uu____61923 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____61923
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _61930  -> FStar_Pervasives_Native.Some _61930)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61932,(u,uu____61934)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____61953 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____61953
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _61960  -> FStar_Pervasives_Native.Some _61960)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61962,(t1,uu____61964)::(b,uu____61966)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____61989 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61989
            (fun b1  ->
               let uu____61995 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61995
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _62002  -> FStar_Pervasives_Native.Some _62002)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62004,(c,uu____62006)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____62025 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____62025
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _62032  -> FStar_Pervasives_Native.Some _62032)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62034,(l,uu____62036)::(u,uu____62038)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____62061 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____62061
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _62070  -> FStar_Pervasives_Native.Some _62070)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62072,(t2,uu____62074)::(t1,uu____62076)::(b,uu____62078)::
           (r,uu____62080)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____62111 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____62111
            (fun r1  ->
               let uu____62121 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____62121
                 (fun b1  ->
                    let uu____62127 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____62127
                      (fun t11  ->
                         let uu____62133 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____62133
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _62140  ->
                                   FStar_Pervasives_Native.Some _62140)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62143,(brs,uu____62145)::(t1,uu____62147)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____62170 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____62170
            (fun t2  ->
               let uu____62176 =
                 let uu____62181 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____62181 cb brs  in
               FStar_Util.bind_opt uu____62176
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _62196  -> FStar_Pervasives_Native.Some _62196)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62200,(tacopt,uu____62202)::(t1,uu____62204)::(e,uu____62206)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____62233 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62233
            (fun e1  ->
               let uu____62239 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____62239
                 (fun t2  ->
                    let uu____62245 =
                      let uu____62250 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62250 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62245
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62265  ->
                              FStar_Pervasives_Native.Some _62265)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62269,(tacopt,uu____62271)::(c,uu____62273)::(e,uu____62275)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____62302 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62302
            (fun e1  ->
               let uu____62308 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____62308
                 (fun c1  ->
                    let uu____62314 =
                      let uu____62319 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62319 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62314
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62334  ->
                              FStar_Pervasives_Native.Some _62334)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____62338,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _62355  -> FStar_Pervasives_Native.Some _62355)
            FStar_Reflection_Data.Tv_Unknown
      | uu____62356 ->
          ((let uu____62358 =
              let uu____62364 =
                let uu____62366 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____62366
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____62364)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____62358);
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
    let uu____62393 =
      let uu____62400 =
        let uu____62405 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____62405  in
      let uu____62407 =
        let uu____62414 =
          let uu____62419 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____62419  in
        let uu____62420 =
          let uu____62427 =
            let uu____62432 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62432  in
          [uu____62427]  in
        uu____62414 :: uu____62420  in
      uu____62400 :: uu____62407  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____62393
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62465,(s,uu____62467)::(idx,uu____62469)::(nm,uu____62471)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____62498 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____62498
          (fun nm1  ->
             let uu____62508 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____62508
               (fun idx1  ->
                  let uu____62514 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____62514
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _62521  -> FStar_Pervasives_Native.Some _62521)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____62522 ->
        ((let uu____62524 =
            let uu____62530 =
              let uu____62532 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____62532
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62530)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62524);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____62556 =
          let uu____62563 =
            let uu____62568 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____62568  in
          let uu____62569 =
            let uu____62576 =
              let uu____62581 =
                let uu____62582 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____62582 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____62581  in
            [uu____62576]  in
          uu____62563 :: uu____62569  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____62556
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____62606 =
          let uu____62613 =
            let uu____62618 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62618  in
          let uu____62619 =
            let uu____62626 =
              let uu____62631 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____62631  in
            [uu____62626]  in
          uu____62613 :: uu____62619  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____62606
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62664,(md,uu____62666)::(t1,uu____62668)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____62691 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____62691
          (fun t2  ->
             let uu____62697 =
               let uu____62702 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____62702 cb md  in
             FStar_Util.bind_opt uu____62697
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _62717  -> FStar_Pervasives_Native.Some _62717)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62721,(post,uu____62723)::(pre,uu____62725)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____62748 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____62748
          (fun pre1  ->
             let uu____62754 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____62754
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _62761  -> FStar_Pervasives_Native.Some _62761)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62763,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _62780  -> FStar_Pervasives_Native.Some _62780)
          FStar_Reflection_Data.C_Unknown
    | uu____62781 ->
        ((let uu____62783 =
            let uu____62789 =
              let uu____62791 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____62791
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62789)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62783);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62837,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62853,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62869,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____62884 ->
        ((let uu____62886 =
            let uu____62892 =
              let uu____62894 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____62894  in
            (FStar_Errors.Warning_NotEmbedded, uu____62892)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62886);
         FStar_Pervasives_Native.None)
     in
  let uu____62898 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____62898 
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
           FStar_Syntax_Syntax.ltyp = uu____62929;
           FStar_Syntax_Syntax.rng = uu____62930;_},uu____62931)
        ->
        let uu____62950 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____62950
    | uu____62951 ->
        ((let uu____62953 =
            let uu____62959 =
              let uu____62961 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____62961  in
            (FStar_Errors.Warning_NotEmbedded, uu____62959)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62953);
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
    let uu____62990 =
      let uu____62996 = FStar_Ident.range_of_id i  in
      let uu____62997 = FStar_Ident.text_of_id i  in
      (uu____62996, uu____62997)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____62990  in
  let unembed_ident cb t =
    let uu____63020 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____63020 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____63044 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____63044
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
    let uu____63054 =
      let uu____63062 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____63064 =
        let uu____63067 = fv_as_emb_typ range_fv  in
        let uu____63068 =
          let uu____63071 = fv_as_emb_typ string_fv  in [uu____63071]  in
        uu____63067 :: uu____63068  in
      (uu____63062, uu____63064)  in
    FStar_Syntax_Syntax.ET_app uu____63054  in
  let uu____63075 =
    let uu____63076 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____63077 =
      let uu____63084 =
        let uu____63089 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____63089  in
      let uu____63094 =
        let uu____63101 =
          let uu____63106 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____63106  in
        [uu____63101]  in
      uu____63084 :: uu____63094  in
    mkFV uu____63076 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____63077
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____63075 et 
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
        let uu____63163 =
          let uu____63170 =
            let uu____63175 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____63175  in
          let uu____63177 =
            let uu____63184 =
              let uu____63189 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63189  in
            let uu____63190 =
              let uu____63197 =
                let uu____63202 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____63202  in
              let uu____63205 =
                let uu____63212 =
                  let uu____63217 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63217  in
                let uu____63218 =
                  let uu____63225 =
                    let uu____63230 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63230  in
                  [uu____63225]  in
                uu____63212 :: uu____63218  in
              uu____63197 :: uu____63205  in
            uu____63184 :: uu____63190  in
          uu____63170 :: uu____63177  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____63163
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____63257 =
          let uu____63264 =
            let uu____63269 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63269  in
          let uu____63273 =
            let uu____63280 =
              let uu____63285 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63285  in
            [uu____63280]  in
          uu____63264 :: uu____63273  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____63257
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____63315 =
          let uu____63322 =
            let uu____63327 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63327  in
          let uu____63331 =
            let uu____63338 =
              let uu____63343 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____63343  in
            let uu____63346 =
              let uu____63353 =
                let uu____63358 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____63358  in
              let uu____63359 =
                let uu____63366 =
                  let uu____63371 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63371  in
                let uu____63372 =
                  let uu____63379 =
                    let uu____63384 =
                      let uu____63385 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____63385 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63384  in
                  [uu____63379]  in
                uu____63366 :: uu____63372  in
              uu____63353 :: uu____63359  in
            uu____63338 :: uu____63346  in
          uu____63322 :: uu____63331  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____63315
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63445,(dcs,uu____63447)::(t1,uu____63449)::(bs,uu____63451)::
         (us,uu____63453)::(nm,uu____63455)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____63490 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____63490
          (fun nm1  ->
             let uu____63508 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____63508
               (fun us1  ->
                  let uu____63522 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____63522
                    (fun bs1  ->
                       let uu____63528 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____63528
                         (fun t2  ->
                            let uu____63534 =
                              let uu____63542 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____63542
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____63534
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _63572  ->
                                      FStar_Pervasives_Native.Some _63572)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63580,(t1,uu____63582)::(ty,uu____63584)::(univs1,uu____63586)::
         (fvar1,uu____63588)::(r,uu____63590)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____63625 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____63625
          (fun r1  ->
             let uu____63635 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____63635
               (fun fvar2  ->
                  let uu____63641 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____63641
                    (fun univs2  ->
                       let uu____63655 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____63655
                         (fun ty1  ->
                            let uu____63661 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____63661
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _63668  ->
                                      FStar_Pervasives_Native.Some _63668)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63673,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____63688 ->
        ((let uu____63690 =
            let uu____63696 =
              let uu____63698 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____63698
               in
            (FStar_Errors.Warning_NotEmbedded, uu____63696)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63690);
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
        let uu____63721 =
          let uu____63728 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____63728]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____63721
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____63743 =
          let uu____63750 =
            let uu____63755 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____63755  in
          let uu____63756 =
            let uu____63763 =
              let uu____63768 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____63768  in
            [uu____63763]  in
          uu____63750 :: uu____63756  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____63743
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63797,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63813,(i,uu____63815)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____63834 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____63834
          (fun i1  ->
             FStar_All.pipe_left
               (fun _63841  -> FStar_Pervasives_Native.Some _63841)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63843,(e2,uu____63845)::(e1,uu____63847)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____63870 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____63870
          (fun e11  ->
             let uu____63876 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____63876
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _63883  -> FStar_Pervasives_Native.Some _63883)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____63884 ->
        ((let uu____63886 =
            let uu____63892 =
              let uu____63894 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____63894  in
            (FStar_Errors.Warning_NotEmbedded, uu____63892)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63886);
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