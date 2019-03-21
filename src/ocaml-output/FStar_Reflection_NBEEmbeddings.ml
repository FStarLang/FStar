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
    let uu____59455 =
      let uu____59463 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____59463, [])  in
    FStar_Syntax_Syntax.ET_app uu____59455
  
let mk_emb' :
  'Auu____59477 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____59477 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____59477 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____59477 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____59519 = mkFV fv [] []  in
        let uu____59524 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____59519 uu____59524
  
let mk_lazy :
  'Auu____59536 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____59536 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____59562 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____59562;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____59568  ->
                 let uu____59569 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____59569)
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
           FStar_Syntax_Syntax.ltyp = uu____59614;
           FStar_Syntax_Syntax.rng = uu____59615;_},uu____59616)
        ->
        let uu____59635 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _59638  -> FStar_Pervasives_Native.Some _59638) uu____59635
    | uu____59639 ->
        ((let uu____59641 =
            let uu____59647 =
              let uu____59649 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____59649  in
            (FStar_Errors.Warning_NotEmbedded, uu____59647)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59641);
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
           FStar_Syntax_Syntax.ltyp = uu____59683;
           FStar_Syntax_Syntax.rng = uu____59684;_},uu____59685)
        ->
        let uu____59704 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59704
    | uu____59705 ->
        ((let uu____59707 =
            let uu____59713 =
              let uu____59715 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____59715  in
            (FStar_Errors.Warning_NotEmbedded, uu____59713)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59707);
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
          let uu____59765 = f x  in
          FStar_Util.bind_opt uu____59765
            (fun x1  ->
               let uu____59773 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59773
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
      | uu____59843 -> FStar_Pervasives_Native.None  in
    let uu____59844 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____59849 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____59844;
      FStar_TypeChecker_NBETerm.emb_typ = uu____59849
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
        let uu____59882 =
          let uu____59889 =
            let uu____59894 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____59894  in
          [uu____59889]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____59882
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____59946)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____59963 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____59963
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____59968 ->
        ((let uu____59970 =
            let uu____59976 =
              let uu____59978 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____59978  in
            (FStar_Errors.Warning_NotEmbedded, uu____59976)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____59970);
         FStar_Pervasives_Native.None)
     in
  let uu____59982 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____59987 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____59982
    uu____59987
  
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
           FStar_Syntax_Syntax.ltyp = uu____60021;
           FStar_Syntax_Syntax.rng = uu____60022;_},uu____60023)
        ->
        let uu____60042 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60042
    | uu____60043 ->
        ((let uu____60045 =
            let uu____60051 =
              let uu____60053 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____60053  in
            (FStar_Errors.Warning_NotEmbedded, uu____60051)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60045);
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
           FStar_Syntax_Syntax.ltyp = uu____60087;
           FStar_Syntax_Syntax.rng = uu____60088;_},uu____60089)
        ->
        let uu____60108 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60108
    | uu____60109 ->
        ((let uu____60111 =
            let uu____60117 =
              let uu____60119 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____60119  in
            (FStar_Errors.Warning_NotEmbedded, uu____60117)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60111);
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
           FStar_Syntax_Syntax.ltyp = uu____60153;
           FStar_Syntax_Syntax.rng = uu____60154;_},uu____60155)
        ->
        let uu____60174 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60174
    | uu____60175 ->
        ((let uu____60177 =
            let uu____60183 =
              let uu____60185 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____60185  in
            (FStar_Errors.Warning_NotEmbedded, uu____60183)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60177);
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
        let uu____60216 =
          let uu____60223 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____60223]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____60216
    | FStar_Reflection_Data.C_String s ->
        let uu____60238 =
          let uu____60245 =
            let uu____60250 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60250  in
          [uu____60245]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____60238
    | FStar_Reflection_Data.C_Range r ->
        let uu____60261 =
          let uu____60268 =
            let uu____60273 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60273  in
          [uu____60268]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____60261
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____60287 =
          let uu____60294 =
            let uu____60299 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____60299  in
          [uu____60294]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____60287
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____60367)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____60384 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____60384
          (fun i1  ->
             FStar_All.pipe_left
               (fun _60391  -> FStar_Pervasives_Native.Some _60391)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____60394)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____60411 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____60411
          (fun s1  ->
             FStar_All.pipe_left
               (fun _60422  -> FStar_Pervasives_Native.Some _60422)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____60425)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____60442 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____60442
          (fun r1  ->
             FStar_All.pipe_left
               (fun _60449  -> FStar_Pervasives_Native.Some _60449)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____60465)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____60482 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____60482
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _60501  -> FStar_Pervasives_Native.Some _60501)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____60502 ->
        ((let uu____60504 =
            let uu____60510 =
              let uu____60512 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____60512  in
            (FStar_Errors.Warning_NotEmbedded, uu____60510)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60504);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____60523  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60536 =
            let uu____60543 =
              let uu____60548 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60548  in
            [uu____60543]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____60536
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60563 =
            let uu____60570 =
              let uu____60575 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60575  in
            let uu____60576 =
              let uu____60583 =
                let uu____60588 =
                  let uu____60589 =
                    let uu____60594 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____60594  in
                  FStar_TypeChecker_NBETerm.embed uu____60589 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____60588  in
              [uu____60583]  in
            uu____60570 :: uu____60576  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____60563
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60612 =
            let uu____60619 =
              let uu____60624 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60624  in
            [uu____60619]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____60612
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____60634 =
            let uu____60641 =
              let uu____60646 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60646  in
            [uu____60641]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____60634
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____60657 =
            let uu____60664 =
              let uu____60669 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____60669  in
            let uu____60670 =
              let uu____60677 =
                let uu____60682 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____60682  in
              [uu____60677]  in
            uu____60664 :: uu____60670  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____60657
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____60712)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____60729 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____60729
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _60736  -> FStar_Pervasives_Native.Some _60736)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____60739)::(f,uu____60741)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____60762 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____60762
            (fun f1  ->
               let uu____60768 =
                 let uu____60773 =
                   let uu____60778 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____60778  in
                 FStar_TypeChecker_NBETerm.unembed uu____60773 cb ps  in
               FStar_Util.bind_opt uu____60768
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _60791  -> FStar_Pervasives_Native.Some _60791)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60796)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____60813 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60813
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60820  -> FStar_Pervasives_Native.Some _60820)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____60823)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____60840 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60840
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _60847  -> FStar_Pervasives_Native.Some _60847)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____60850)::(bv,uu____60852)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____60873 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____60873
            (fun bv1  ->
               let uu____60879 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____60879
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _60886  -> FStar_Pervasives_Native.Some _60886)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____60887 ->
          ((let uu____60889 =
              let uu____60895 =
                let uu____60897 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____60897
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____60895)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____60889);
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
    let uu____60938 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____60938
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____60969 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____60969 e_aqualv
  
let rec unlazy_as_t :
  'Auu____60979 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____60979
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____60992;
             FStar_Syntax_Syntax.rng = uu____60993;_},uu____60994)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____61013 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61051 =
            let uu____61058 =
              let uu____61063 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61063  in
            [uu____61058]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____61051
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____61073 =
            let uu____61080 =
              let uu____61085 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61085  in
            [uu____61080]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____61073
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61095 =
            let uu____61102 =
              let uu____61107 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61107  in
            [uu____61102]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____61095
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61118 =
            let uu____61125 =
              let uu____61130 =
                let uu____61131 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61131 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____61130  in
            let uu____61134 =
              let uu____61141 =
                let uu____61146 =
                  let uu____61147 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61147 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____61146  in
              [uu____61141]  in
            uu____61125 :: uu____61134  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____61118
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____61172 =
            let uu____61179 =
              let uu____61184 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61184  in
            let uu____61185 =
              let uu____61192 =
                let uu____61197 =
                  let uu____61198 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61198 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61197  in
              [uu____61192]  in
            uu____61179 :: uu____61185  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____61172
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61215 =
            let uu____61222 =
              let uu____61227 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61227  in
            let uu____61228 =
              let uu____61235 =
                let uu____61240 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61240  in
              [uu____61235]  in
            uu____61222 :: uu____61228  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____61215
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61254 =
            let uu____61261 =
              let uu____61266 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61266  in
            [uu____61261]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____61254
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____61277 =
            let uu____61284 =
              let uu____61289 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61289  in
            let uu____61290 =
              let uu____61297 =
                let uu____61302 =
                  let uu____61303 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61303 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61302  in
              [uu____61297]  in
            uu____61284 :: uu____61290  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____61277
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61319 =
            let uu____61326 =
              let uu____61331 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61331  in
            [uu____61326]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____61319
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61342 =
            let uu____61349 =
              let uu____61354 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61354  in
            let uu____61355 =
              let uu____61362 =
                let uu____61367 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61367  in
              [uu____61362]  in
            uu____61349 :: uu____61355  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____61342
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____61390 =
            let uu____61397 =
              let uu____61402 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61402  in
            let uu____61404 =
              let uu____61411 =
                let uu____61416 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61416  in
              let uu____61417 =
                let uu____61424 =
                  let uu____61429 =
                    let uu____61430 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____61430 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61429  in
                let uu____61433 =
                  let uu____61440 =
                    let uu____61445 =
                      let uu____61446 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____61446 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____61445  in
                  [uu____61440]  in
                uu____61424 :: uu____61433  in
              uu____61411 :: uu____61417  in
            uu____61397 :: uu____61404  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____61390
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____61475 =
            let uu____61482 =
              let uu____61487 =
                let uu____61488 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61488 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____61487  in
            let uu____61491 =
              let uu____61498 =
                let uu____61503 =
                  let uu____61504 =
                    let uu____61513 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____61513  in
                  FStar_TypeChecker_NBETerm.embed uu____61504 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____61503  in
              [uu____61498]  in
            uu____61482 :: uu____61491  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____61475
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____61549 =
            let uu____61556 =
              let uu____61561 =
                let uu____61562 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61562 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61561  in
            let uu____61565 =
              let uu____61572 =
                let uu____61577 =
                  let uu____61578 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61578 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61577  in
              let uu____61581 =
                let uu____61588 =
                  let uu____61593 =
                    let uu____61594 =
                      let uu____61599 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61599  in
                    FStar_TypeChecker_NBETerm.embed uu____61594 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61593  in
                [uu____61588]  in
              uu____61572 :: uu____61581  in
            uu____61556 :: uu____61565  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61549
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____61627 =
            let uu____61634 =
              let uu____61639 =
                let uu____61640 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61640 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____61639  in
            let uu____61643 =
              let uu____61650 =
                let uu____61655 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61655  in
              let uu____61656 =
                let uu____61663 =
                  let uu____61668 =
                    let uu____61669 =
                      let uu____61674 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____61674  in
                    FStar_TypeChecker_NBETerm.embed uu____61669 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____61668  in
                [uu____61663]  in
              uu____61650 :: uu____61656  in
            uu____61634 :: uu____61643  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____61627
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61715,(b,uu____61717)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____61736 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61736
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61743  -> FStar_Pervasives_Native.Some _61743)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61745,(b,uu____61747)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____61766 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61766
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _61773  -> FStar_Pervasives_Native.Some _61773)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61775,(f,uu____61777)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____61796 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____61796
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _61803  -> FStar_Pervasives_Native.Some _61803)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61805,(r,uu____61807)::(l,uu____61809)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____61832 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____61832
            (fun l1  ->
               let uu____61838 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____61838
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _61845  -> FStar_Pervasives_Native.Some _61845)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61847,(t1,uu____61849)::(b,uu____61851)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____61874 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61874
            (fun b1  ->
               let uu____61880 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61880
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _61887  -> FStar_Pervasives_Native.Some _61887)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61889,(t1,uu____61891)::(b,uu____61893)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____61916 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____61916
            (fun b1  ->
               let uu____61922 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____61922
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _61929  -> FStar_Pervasives_Native.Some _61929)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61931,(u,uu____61933)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____61952 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____61952
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _61959  -> FStar_Pervasives_Native.Some _61959)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____61961,(t1,uu____61963)::(b,uu____61965)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____61988 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____61988
            (fun b1  ->
               let uu____61994 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61994
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _62001  -> FStar_Pervasives_Native.Some _62001)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62003,(c,uu____62005)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____62024 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____62024
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _62031  -> FStar_Pervasives_Native.Some _62031)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62033,(l,uu____62035)::(u,uu____62037)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____62060 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____62060
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _62069  -> FStar_Pervasives_Native.Some _62069)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62071,(t2,uu____62073)::(t1,uu____62075)::(b,uu____62077)::
           (r,uu____62079)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____62110 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____62110
            (fun r1  ->
               let uu____62120 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____62120
                 (fun b1  ->
                    let uu____62126 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____62126
                      (fun t11  ->
                         let uu____62132 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____62132
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _62139  ->
                                   FStar_Pervasives_Native.Some _62139)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62142,(brs,uu____62144)::(t1,uu____62146)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____62169 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____62169
            (fun t2  ->
               let uu____62175 =
                 let uu____62180 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____62180 cb brs  in
               FStar_Util.bind_opt uu____62175
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _62195  -> FStar_Pervasives_Native.Some _62195)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62199,(tacopt,uu____62201)::(t1,uu____62203)::(e,uu____62205)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____62232 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62232
            (fun e1  ->
               let uu____62238 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____62238
                 (fun t2  ->
                    let uu____62244 =
                      let uu____62249 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62249 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62244
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62264  ->
                              FStar_Pervasives_Native.Some _62264)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62268,(tacopt,uu____62270)::(c,uu____62272)::(e,uu____62274)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____62301 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62301
            (fun e1  ->
               let uu____62307 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____62307
                 (fun c1  ->
                    let uu____62313 =
                      let uu____62318 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____62318 cb tacopt
                       in
                    FStar_Util.bind_opt uu____62313
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _62333  ->
                              FStar_Pervasives_Native.Some _62333)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____62337,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _62354  -> FStar_Pervasives_Native.Some _62354)
            FStar_Reflection_Data.Tv_Unknown
      | uu____62355 ->
          ((let uu____62357 =
              let uu____62363 =
                let uu____62365 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____62365
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____62363)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____62357);
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
    let uu____62392 =
      let uu____62399 =
        let uu____62404 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____62404  in
      let uu____62406 =
        let uu____62413 =
          let uu____62418 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____62418  in
        let uu____62419 =
          let uu____62426 =
            let uu____62431 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62431  in
          [uu____62426]  in
        uu____62413 :: uu____62419  in
      uu____62399 :: uu____62406  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____62392
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62464,(s,uu____62466)::(idx,uu____62468)::(nm,uu____62470)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____62497 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____62497
          (fun nm1  ->
             let uu____62507 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____62507
               (fun idx1  ->
                  let uu____62513 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____62513
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _62520  -> FStar_Pervasives_Native.Some _62520)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____62521 ->
        ((let uu____62523 =
            let uu____62529 =
              let uu____62531 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____62531
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62529)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62523);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____62555 =
          let uu____62562 =
            let uu____62567 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____62567  in
          let uu____62568 =
            let uu____62575 =
              let uu____62580 =
                let uu____62581 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____62581 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____62580  in
            [uu____62575]  in
          uu____62562 :: uu____62568  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____62555
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____62605 =
          let uu____62612 =
            let uu____62617 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____62617  in
          let uu____62618 =
            let uu____62625 =
              let uu____62630 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____62630  in
            [uu____62625]  in
          uu____62612 :: uu____62618  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____62605
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62663,(md,uu____62665)::(t1,uu____62667)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____62690 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____62690
          (fun t2  ->
             let uu____62696 =
               let uu____62701 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____62701 cb md  in
             FStar_Util.bind_opt uu____62696
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _62716  -> FStar_Pervasives_Native.Some _62716)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____62720,(post,uu____62722)::(pre,uu____62724)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____62747 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____62747
          (fun pre1  ->
             let uu____62753 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____62753
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _62760  -> FStar_Pervasives_Native.Some _62760)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62762,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _62779  -> FStar_Pervasives_Native.Some _62779)
          FStar_Reflection_Data.C_Unknown
    | uu____62780 ->
        ((let uu____62782 =
            let uu____62788 =
              let uu____62790 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____62790
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62788)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62782);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62836,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62852,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____62868,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____62883 ->
        ((let uu____62885 =
            let uu____62891 =
              let uu____62893 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____62893  in
            (FStar_Errors.Warning_NotEmbedded, uu____62891)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62885);
         FStar_Pervasives_Native.None)
     in
  let uu____62897 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____62897 
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
           FStar_Syntax_Syntax.ltyp = uu____62928;
           FStar_Syntax_Syntax.rng = uu____62929;_},uu____62930)
        ->
        let uu____62949 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____62949
    | uu____62950 ->
        ((let uu____62952 =
            let uu____62958 =
              let uu____62960 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____62960  in
            (FStar_Errors.Warning_NotEmbedded, uu____62958)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62952);
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
    let uu____62989 =
      let uu____62995 = FStar_Ident.range_of_id i  in
      let uu____62996 = FStar_Ident.text_of_id i  in
      (uu____62995, uu____62996)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____62989  in
  let unembed_ident cb t =
    let uu____63019 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____63019 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____63043 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____63043
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
    let uu____63053 =
      let uu____63061 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____63063 =
        let uu____63066 = fv_as_emb_typ range_fv  in
        let uu____63067 =
          let uu____63070 = fv_as_emb_typ string_fv  in [uu____63070]  in
        uu____63066 :: uu____63067  in
      (uu____63061, uu____63063)  in
    FStar_Syntax_Syntax.ET_app uu____63053  in
  let uu____63074 =
    let uu____63075 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____63076 =
      let uu____63083 =
        let uu____63088 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____63088  in
      let uu____63093 =
        let uu____63100 =
          let uu____63105 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____63105  in
        [uu____63100]  in
      uu____63083 :: uu____63093  in
    mkFV uu____63075 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____63076
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____63074 et 
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
        let uu____63162 =
          let uu____63169 =
            let uu____63174 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____63174  in
          let uu____63176 =
            let uu____63183 =
              let uu____63188 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63188  in
            let uu____63189 =
              let uu____63196 =
                let uu____63201 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____63201  in
              let uu____63204 =
                let uu____63211 =
                  let uu____63216 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63216  in
                let uu____63217 =
                  let uu____63224 =
                    let uu____63229 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63229  in
                  [uu____63224]  in
                uu____63211 :: uu____63217  in
              uu____63196 :: uu____63204  in
            uu____63183 :: uu____63189  in
          uu____63169 :: uu____63176  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____63162
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____63256 =
          let uu____63263 =
            let uu____63268 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63268  in
          let uu____63272 =
            let uu____63279 =
              let uu____63284 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63284  in
            [uu____63279]  in
          uu____63263 :: uu____63272  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____63256
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____63314 =
          let uu____63321 =
            let uu____63326 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____63326  in
          let uu____63330 =
            let uu____63337 =
              let uu____63342 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____63342  in
            let uu____63345 =
              let uu____63352 =
                let uu____63357 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____63357  in
              let uu____63358 =
                let uu____63365 =
                  let uu____63370 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63370  in
                let uu____63371 =
                  let uu____63378 =
                    let uu____63383 =
                      let uu____63384 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____63384 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63383  in
                  [uu____63378]  in
                uu____63365 :: uu____63371  in
              uu____63352 :: uu____63358  in
            uu____63337 :: uu____63345  in
          uu____63321 :: uu____63330  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____63314
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63444,(dcs,uu____63446)::(t1,uu____63448)::(bs,uu____63450)::
         (us,uu____63452)::(nm,uu____63454)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____63489 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____63489
          (fun nm1  ->
             let uu____63507 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____63507
               (fun us1  ->
                  let uu____63521 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____63521
                    (fun bs1  ->
                       let uu____63527 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____63527
                         (fun t2  ->
                            let uu____63533 =
                              let uu____63541 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____63541
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____63533
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _63571  ->
                                      FStar_Pervasives_Native.Some _63571)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63579,(t1,uu____63581)::(ty,uu____63583)::(univs1,uu____63585)::
         (fvar1,uu____63587)::(r,uu____63589)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____63624 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____63624
          (fun r1  ->
             let uu____63634 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____63634
               (fun fvar2  ->
                  let uu____63640 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____63640
                    (fun univs2  ->
                       let uu____63654 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____63654
                         (fun ty1  ->
                            let uu____63660 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____63660
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _63667  ->
                                      FStar_Pervasives_Native.Some _63667)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63672,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____63687 ->
        ((let uu____63689 =
            let uu____63695 =
              let uu____63697 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____63697
               in
            (FStar_Errors.Warning_NotEmbedded, uu____63695)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63689);
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
        let uu____63720 =
          let uu____63727 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____63727]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____63720
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____63742 =
          let uu____63749 =
            let uu____63754 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____63754  in
          let uu____63755 =
            let uu____63762 =
              let uu____63767 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____63767  in
            [uu____63762]  in
          uu____63749 :: uu____63755  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____63742
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63796,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63812,(i,uu____63814)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____63833 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____63833
          (fun i1  ->
             FStar_All.pipe_left
               (fun _63840  -> FStar_Pervasives_Native.Some _63840)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63842,(e2,uu____63844)::(e1,uu____63846)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____63869 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____63869
          (fun e11  ->
             let uu____63875 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____63875
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _63882  -> FStar_Pervasives_Native.Some _63882)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____63883 ->
        ((let uu____63885 =
            let uu____63891 =
              let uu____63893 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____63893  in
            (FStar_Errors.Warning_NotEmbedded, uu____63891)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63885);
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