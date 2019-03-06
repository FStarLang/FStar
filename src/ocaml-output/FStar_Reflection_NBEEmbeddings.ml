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
    let uu____60220 =
      let uu____60228 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____60228, [])  in
    FStar_Syntax_Syntax.ET_app uu____60220
  
let mk_emb' :
  'Auu____60242 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____60242 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____60242 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____60242 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____60284 = mkFV fv [] []  in
        let uu____60289 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____60284 uu____60289
  
let mk_lazy :
  'Auu____60301 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____60301 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____60327 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____60327;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Common.mk_thunk
              (fun uu____60333  ->
                 let uu____60334 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____60334)
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
           FStar_Syntax_Syntax.ltyp = uu____60379;
           FStar_Syntax_Syntax.rng = uu____60380;_},uu____60381)
        ->
        let uu____60400 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _60403  -> FStar_Pervasives_Native.Some _60403) uu____60400
    | uu____60404 ->
        ((let uu____60406 =
            let uu____60412 =
              let uu____60414 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____60414  in
            (FStar_Errors.Warning_NotEmbedded, uu____60412)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60406);
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
           FStar_Syntax_Syntax.ltyp = uu____60448;
           FStar_Syntax_Syntax.rng = uu____60449;_},uu____60450)
        ->
        let uu____60469 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60469
    | uu____60470 ->
        ((let uu____60472 =
            let uu____60478 =
              let uu____60480 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____60480  in
            (FStar_Errors.Warning_NotEmbedded, uu____60478)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60472);
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
          let uu____60530 = f x  in
          FStar_Util.bind_opt uu____60530
            (fun x1  ->
               let uu____60538 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____60538
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
      | uu____60608 -> FStar_Pervasives_Native.None  in
    let uu____60609 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____60614 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____60609;
      FStar_TypeChecker_NBETerm.emb_typ = uu____60614
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
        let uu____60647 =
          let uu____60654 =
            let uu____60659 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____60659  in
          [uu____60654]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____60647
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____60711)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____60728 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____60728
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____60733 ->
        ((let uu____60735 =
            let uu____60741 =
              let uu____60743 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____60743  in
            (FStar_Errors.Warning_NotEmbedded, uu____60741)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60735);
         FStar_Pervasives_Native.None)
     in
  let uu____60747 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____60752 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____60747
    uu____60752
  
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
           FStar_Syntax_Syntax.ltyp = uu____60786;
           FStar_Syntax_Syntax.rng = uu____60787;_},uu____60788)
        ->
        let uu____60807 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60807
    | uu____60808 ->
        ((let uu____60810 =
            let uu____60816 =
              let uu____60818 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____60818  in
            (FStar_Errors.Warning_NotEmbedded, uu____60816)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60810);
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
           FStar_Syntax_Syntax.ltyp = uu____60852;
           FStar_Syntax_Syntax.rng = uu____60853;_},uu____60854)
        ->
        let uu____60873 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60873
    | uu____60874 ->
        ((let uu____60876 =
            let uu____60882 =
              let uu____60884 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____60884  in
            (FStar_Errors.Warning_NotEmbedded, uu____60882)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60876);
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
           FStar_Syntax_Syntax.ltyp = uu____60918;
           FStar_Syntax_Syntax.rng = uu____60919;_},uu____60920)
        ->
        let uu____60939 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60939
    | uu____60940 ->
        ((let uu____60942 =
            let uu____60948 =
              let uu____60950 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____60950  in
            (FStar_Errors.Warning_NotEmbedded, uu____60948)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____60942);
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
        let uu____60981 =
          let uu____60988 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____60988]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____60981
    | FStar_Reflection_Data.C_String s ->
        let uu____61003 =
          let uu____61010 =
            let uu____61015 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____61015  in
          [uu____61010]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____61003
    | FStar_Reflection_Data.C_Range r ->
        let uu____61026 =
          let uu____61033 =
            let uu____61038 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____61038  in
          [uu____61033]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____61026
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____61052 =
          let uu____61059 =
            let uu____61064 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____61064  in
          [uu____61059]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____61052
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____61132)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____61149 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____61149
          (fun i1  ->
             FStar_All.pipe_left
               (fun _61156  -> FStar_Pervasives_Native.Some _61156)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____61159)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____61176 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____61176
          (fun s1  ->
             FStar_All.pipe_left
               (fun _61187  -> FStar_Pervasives_Native.Some _61187)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____61190)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____61207 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____61207
          (fun r1  ->
             FStar_All.pipe_left
               (fun _61214  -> FStar_Pervasives_Native.Some _61214)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____61230)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____61247 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____61247
          (fun ns1  ->
             FStar_All.pipe_left
               (fun _61266  -> FStar_Pervasives_Native.Some _61266)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____61267 ->
        ((let uu____61269 =
            let uu____61275 =
              let uu____61277 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____61277  in
            (FStar_Errors.Warning_NotEmbedded, uu____61275)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____61269);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____61288  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____61301 =
            let uu____61308 =
              let uu____61313 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61313  in
            [uu____61308]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____61301
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____61328 =
            let uu____61335 =
              let uu____61340 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61340  in
            let uu____61341 =
              let uu____61348 =
                let uu____61353 =
                  let uu____61354 =
                    let uu____61359 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____61359  in
                  FStar_TypeChecker_NBETerm.embed uu____61354 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____61353  in
              [uu____61348]  in
            uu____61335 :: uu____61341  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____61328
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____61377 =
            let uu____61384 =
              let uu____61389 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61389  in
            [uu____61384]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____61377
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____61399 =
            let uu____61406 =
              let uu____61411 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61411  in
            [uu____61406]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____61399
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____61422 =
            let uu____61429 =
              let uu____61434 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61434  in
            let uu____61435 =
              let uu____61442 =
                let uu____61447 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____61447  in
              [uu____61442]  in
            uu____61429 :: uu____61435  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____61422
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____61477)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____61494 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____61494
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _61501  -> FStar_Pervasives_Native.Some _61501)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____61504)::(f,uu____61506)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____61527 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____61527
            (fun f1  ->
               let uu____61533 =
                 let uu____61538 =
                   let uu____61543 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____61543  in
                 FStar_TypeChecker_NBETerm.unembed uu____61538 cb ps  in
               FStar_Util.bind_opt uu____61533
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _61556  -> FStar_Pervasives_Native.Some _61556)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____61561)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____61578 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____61578
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _61585  -> FStar_Pervasives_Native.Some _61585)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____61588)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____61605 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____61605
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _61612  -> FStar_Pervasives_Native.Some _61612)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____61615)::(bv,uu____61617)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____61638 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____61638
            (fun bv1  ->
               let uu____61644 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____61644
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _61651  -> FStar_Pervasives_Native.Some _61651)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____61652 ->
          ((let uu____61654 =
              let uu____61660 =
                let uu____61662 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____61662
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____61660)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____61654);
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
    let uu____61703 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____61703
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____61734 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____61734 e_aqualv
  
let rec unlazy_as_t :
  'Auu____61744 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____61744
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____61757;
             FStar_Syntax_Syntax.rng = uu____61758;_},uu____61759)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____61778 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61816 =
            let uu____61823 =
              let uu____61828 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61828  in
            [uu____61823]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____61816
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____61838 =
            let uu____61845 =
              let uu____61850 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61850  in
            [uu____61845]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____61838
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61860 =
            let uu____61867 =
              let uu____61872 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61872  in
            [uu____61867]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____61860
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61883 =
            let uu____61890 =
              let uu____61895 =
                let uu____61896 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____61896 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____61895  in
            let uu____61899 =
              let uu____61906 =
                let uu____61911 =
                  let uu____61912 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61912 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____61911  in
              [uu____61906]  in
            uu____61890 :: uu____61899  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____61883
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____61937 =
            let uu____61944 =
              let uu____61949 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61949  in
            let uu____61950 =
              let uu____61957 =
                let uu____61962 =
                  let uu____61963 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____61963 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____61962  in
              [uu____61957]  in
            uu____61944 :: uu____61950  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____61937
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61980 =
            let uu____61987 =
              let uu____61992 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____61992  in
            let uu____61993 =
              let uu____62000 =
                let uu____62005 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____62005  in
              [uu____62000]  in
            uu____61987 :: uu____61993  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____61980
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____62019 =
            let uu____62026 =
              let uu____62031 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____62031  in
            [uu____62026]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____62019
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____62042 =
            let uu____62049 =
              let uu____62054 = FStar_TypeChecker_NBETerm.embed e_bv cb bv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____62054  in
            let uu____62055 =
              let uu____62062 =
                let uu____62067 =
                  let uu____62068 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____62068 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____62067  in
              [uu____62062]  in
            uu____62049 :: uu____62055  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____62042
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____62084 =
            let uu____62091 =
              let uu____62096 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____62096  in
            [uu____62091]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____62084
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____62107 =
            let uu____62114 =
              let uu____62119 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____62119  in
            let uu____62120 =
              let uu____62127 =
                let uu____62132 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____62132  in
              [uu____62127]  in
            uu____62114 :: uu____62120  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____62107
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____62155 =
            let uu____62162 =
              let uu____62167 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____62167  in
            let uu____62169 =
              let uu____62176 =
                let uu____62181 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____62181  in
              let uu____62182 =
                let uu____62189 =
                  let uu____62194 =
                    let uu____62195 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____62195 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____62194  in
                let uu____62198 =
                  let uu____62205 =
                    let uu____62210 =
                      let uu____62211 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____62211 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____62210  in
                  [uu____62205]  in
                uu____62189 :: uu____62198  in
              uu____62176 :: uu____62182  in
            uu____62162 :: uu____62169  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____62155
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____62240 =
            let uu____62247 =
              let uu____62252 =
                let uu____62253 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____62253 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____62252  in
            let uu____62256 =
              let uu____62263 =
                let uu____62268 =
                  let uu____62269 =
                    let uu____62278 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____62278  in
                  FStar_TypeChecker_NBETerm.embed uu____62269 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____62268  in
              [uu____62263]  in
            uu____62247 :: uu____62256  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____62240
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____62314 =
            let uu____62321 =
              let uu____62326 =
                let uu____62327 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____62327 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____62326  in
            let uu____62330 =
              let uu____62337 =
                let uu____62342 =
                  let uu____62343 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____62343 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____62342  in
              let uu____62346 =
                let uu____62353 =
                  let uu____62358 =
                    let uu____62359 =
                      let uu____62364 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____62364  in
                    FStar_TypeChecker_NBETerm.embed uu____62359 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____62358  in
                [uu____62353]  in
              uu____62337 :: uu____62346  in
            uu____62321 :: uu____62330  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____62314
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____62392 =
            let uu____62399 =
              let uu____62404 =
                let uu____62405 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____62405 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____62404  in
            let uu____62408 =
              let uu____62415 =
                let uu____62420 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____62420  in
              let uu____62421 =
                let uu____62428 =
                  let uu____62433 =
                    let uu____62434 =
                      let uu____62439 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____62439  in
                    FStar_TypeChecker_NBETerm.embed uu____62434 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____62433  in
                [uu____62428]  in
              uu____62415 :: uu____62421  in
            uu____62399 :: uu____62408  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____62392
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62480,(b,uu____62482)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____62501 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____62501
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _62508  -> FStar_Pervasives_Native.Some _62508)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62510,(b,uu____62512)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____62531 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____62531
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _62538  -> FStar_Pervasives_Native.Some _62538)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62540,(f,uu____62542)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____62561 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____62561
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _62568  -> FStar_Pervasives_Native.Some _62568)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62570,(r,uu____62572)::(l,uu____62574)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____62597 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____62597
            (fun l1  ->
               let uu____62603 =
                 FStar_TypeChecker_NBETerm.unembed e_argv cb r  in
               FStar_Util.bind_opt uu____62603
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _62610  -> FStar_Pervasives_Native.Some _62610)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62612,(t1,uu____62614)::(b,uu____62616)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____62639 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____62639
            (fun b1  ->
               let uu____62645 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____62645
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _62652  -> FStar_Pervasives_Native.Some _62652)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62654,(t1,uu____62656)::(b,uu____62658)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____62681 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____62681
            (fun b1  ->
               let uu____62687 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____62687
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _62694  -> FStar_Pervasives_Native.Some _62694)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62696,(u,uu____62698)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____62717 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____62717
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _62724  -> FStar_Pervasives_Native.Some _62724)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62726,(t1,uu____62728)::(b,uu____62730)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____62753 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____62753
            (fun b1  ->
               let uu____62759 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____62759
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _62766  -> FStar_Pervasives_Native.Some _62766)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62768,(c,uu____62770)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____62789 = FStar_TypeChecker_NBETerm.unembed e_const cb c
             in
          FStar_Util.bind_opt uu____62789
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _62796  -> FStar_Pervasives_Native.Some _62796)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62798,(l,uu____62800)::(u,uu____62802)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____62825 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____62825
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _62834  -> FStar_Pervasives_Native.Some _62834)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62836,(t2,uu____62838)::(t1,uu____62840)::(b,uu____62842)::
           (r,uu____62844)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____62875 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____62875
            (fun r1  ->
               let uu____62885 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____62885
                 (fun b1  ->
                    let uu____62891 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____62891
                      (fun t11  ->
                         let uu____62897 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____62897
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _62904  ->
                                   FStar_Pervasives_Native.Some _62904)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62907,(brs,uu____62909)::(t1,uu____62911)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____62934 = FStar_TypeChecker_NBETerm.unembed e_term cb t1
             in
          FStar_Util.bind_opt uu____62934
            (fun t2  ->
               let uu____62940 =
                 let uu____62945 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____62945 cb brs  in
               FStar_Util.bind_opt uu____62940
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _62960  -> FStar_Pervasives_Native.Some _62960)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____62964,(tacopt,uu____62966)::(t1,uu____62968)::(e,uu____62970)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____62997 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____62997
            (fun e1  ->
               let uu____63003 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____63003
                 (fun t2  ->
                    let uu____63009 =
                      let uu____63014 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____63014 cb tacopt
                       in
                    FStar_Util.bind_opt uu____63009
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _63029  ->
                              FStar_Pervasives_Native.Some _63029)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____63033,(tacopt,uu____63035)::(c,uu____63037)::(e,uu____63039)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____63066 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____63066
            (fun e1  ->
               let uu____63072 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb c  in
               FStar_Util.bind_opt uu____63072
                 (fun c1  ->
                    let uu____63078 =
                      let uu____63083 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____63083 cb tacopt
                       in
                    FStar_Util.bind_opt uu____63078
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _63098  ->
                              FStar_Pervasives_Native.Some _63098)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____63102,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _63119  -> FStar_Pervasives_Native.Some _63119)
            FStar_Reflection_Data.Tv_Unknown
      | uu____63120 ->
          ((let uu____63122 =
              let uu____63128 =
                let uu____63130 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s"
                  uu____63130
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____63128)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____63122);
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
    let uu____63157 =
      let uu____63164 =
        let uu____63169 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____63169  in
      let uu____63171 =
        let uu____63178 =
          let uu____63183 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____63183  in
        let uu____63184 =
          let uu____63191 =
            let uu____63196 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____63196  in
          [uu____63191]  in
        uu____63178 :: uu____63184  in
      uu____63164 :: uu____63171  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____63157
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63229,(s,uu____63231)::(idx,uu____63233)::(nm,uu____63235)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____63262 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____63262
          (fun nm1  ->
             let uu____63272 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____63272
               (fun idx1  ->
                  let uu____63278 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____63278
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _63285  -> FStar_Pervasives_Native.Some _63285)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____63286 ->
        ((let uu____63288 =
            let uu____63294 =
              let uu____63296 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____63296
               in
            (FStar_Errors.Warning_NotEmbedded, uu____63294)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63288);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____63320 =
          let uu____63327 =
            let uu____63332 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____63332  in
          let uu____63333 =
            let uu____63340 =
              let uu____63345 =
                let uu____63346 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____63346 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____63345  in
            [uu____63340]  in
          uu____63327 :: uu____63333  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____63320
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____63370 =
          let uu____63377 =
            let uu____63382 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____63382  in
          let uu____63383 =
            let uu____63390 =
              let uu____63395 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____63395  in
            [uu____63390]  in
          uu____63377 :: uu____63383  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____63370
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63428,(md,uu____63430)::(t1,uu____63432)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____63455 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____63455
          (fun t2  ->
             let uu____63461 =
               let uu____63466 = FStar_TypeChecker_NBETerm.e_option e_term
                  in
               FStar_TypeChecker_NBETerm.unembed uu____63466 cb md  in
             FStar_Util.bind_opt uu____63461
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _63481  -> FStar_Pervasives_Native.Some _63481)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____63485,(post,uu____63487)::(pre,uu____63489)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____63512 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____63512
          (fun pre1  ->
             let uu____63518 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____63518
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _63525  -> FStar_Pervasives_Native.Some _63525)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63527,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _63544  -> FStar_Pervasives_Native.Some _63544)
          FStar_Reflection_Data.C_Unknown
    | uu____63545 ->
        ((let uu____63547 =
            let uu____63553 =
              let uu____63555 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____63555
               in
            (FStar_Errors.Warning_NotEmbedded, uu____63553)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63547);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63601,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63617,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____63633,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____63648 ->
        ((let uu____63650 =
            let uu____63656 =
              let uu____63658 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____63658  in
            (FStar_Errors.Warning_NotEmbedded, uu____63656)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63650);
         FStar_Pervasives_Native.None)
     in
  let uu____63662 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____63662 
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
           FStar_Syntax_Syntax.ltyp = uu____63693;
           FStar_Syntax_Syntax.rng = uu____63694;_},uu____63695)
        ->
        let uu____63714 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____63714
    | uu____63715 ->
        ((let uu____63717 =
            let uu____63723 =
              let uu____63725 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____63725  in
            (FStar_Errors.Warning_NotEmbedded, uu____63723)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____63717);
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
    let uu____63754 =
      let uu____63760 = FStar_Ident.range_of_id i  in
      let uu____63761 = FStar_Ident.text_of_id i  in
      (uu____63760, uu____63761)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____63754  in
  let unembed_ident cb t =
    let uu____63784 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____63784 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____63808 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____63808
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
    let uu____63818 =
      let uu____63826 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____63828 =
        let uu____63831 = fv_as_emb_typ range_fv  in
        let uu____63832 =
          let uu____63835 = fv_as_emb_typ string_fv  in [uu____63835]  in
        uu____63831 :: uu____63832  in
      (uu____63826, uu____63828)  in
    FStar_Syntax_Syntax.ET_app uu____63818  in
  let uu____63839 =
    let uu____63840 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____63841 =
      let uu____63848 =
        let uu____63853 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____63853  in
      let uu____63858 =
        let uu____63865 =
          let uu____63870 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____63870  in
        [uu____63865]  in
      uu____63848 :: uu____63858  in
    mkFV uu____63840 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____63841
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____63839 et 
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
        let uu____63927 =
          let uu____63934 =
            let uu____63939 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____63939  in
          let uu____63941 =
            let uu____63948 =
              let uu____63953 = FStar_TypeChecker_NBETerm.embed e_fv cb fv
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____63953  in
            let uu____63954 =
              let uu____63961 =
                let uu____63966 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____63966  in
              let uu____63969 =
                let uu____63976 =
                  let uu____63981 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____63981  in
                let uu____63982 =
                  let uu____63989 =
                    let uu____63994 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____63994  in
                  [uu____63989]  in
                uu____63976 :: uu____63982  in
              uu____63961 :: uu____63969  in
            uu____63948 :: uu____63954  in
          uu____63934 :: uu____63941  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____63927
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____64021 =
          let uu____64028 =
            let uu____64033 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____64033  in
          let uu____64037 =
            let uu____64044 =
              let uu____64049 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____64049  in
            [uu____64044]  in
          uu____64028 :: uu____64037  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____64021
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____64079 =
          let uu____64086 =
            let uu____64091 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____64091  in
          let uu____64095 =
            let uu____64102 =
              let uu____64107 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____64107  in
            let uu____64110 =
              let uu____64117 =
                let uu____64122 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____64122  in
              let uu____64123 =
                let uu____64130 =
                  let uu____64135 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____64135  in
                let uu____64136 =
                  let uu____64143 =
                    let uu____64148 =
                      let uu____64149 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____64149 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____64148  in
                  [uu____64143]  in
                uu____64130 :: uu____64136  in
              uu____64117 :: uu____64123  in
            uu____64102 :: uu____64110  in
          uu____64086 :: uu____64095  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____64079
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____64209,(dcs,uu____64211)::(t1,uu____64213)::(bs,uu____64215)::
         (us,uu____64217)::(nm,uu____64219)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____64254 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____64254
          (fun nm1  ->
             let uu____64272 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____64272
               (fun us1  ->
                  let uu____64286 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____64286
                    (fun bs1  ->
                       let uu____64292 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____64292
                         (fun t2  ->
                            let uu____64298 =
                              let uu____64306 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____64306
                                cb dcs
                               in
                            FStar_Util.bind_opt uu____64298
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _64336  ->
                                      FStar_Pervasives_Native.Some _64336)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____64344,(t1,uu____64346)::(ty,uu____64348)::(univs1,uu____64350)::
         (fvar1,uu____64352)::(r,uu____64354)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____64389 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____64389
          (fun r1  ->
             let uu____64399 =
               FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1  in
             FStar_Util.bind_opt uu____64399
               (fun fvar2  ->
                  let uu____64405 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____64405
                    (fun univs2  ->
                       let uu____64419 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____64419
                         (fun ty1  ->
                            let uu____64425 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____64425
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _64432  ->
                                      FStar_Pervasives_Native.Some _64432)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____64437,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____64452 ->
        ((let uu____64454 =
            let uu____64460 =
              let uu____64462 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s"
                uu____64462
               in
            (FStar_Errors.Warning_NotEmbedded, uu____64460)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64454);
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
        let uu____64485 =
          let uu____64492 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____64492]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____64485
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____64507 =
          let uu____64514 =
            let uu____64519 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____64519  in
          let uu____64520 =
            let uu____64527 =
              let uu____64532 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____64532  in
            [uu____64527]  in
          uu____64514 :: uu____64520  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____64507
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____64561,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____64577,(i,uu____64579)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____64598 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____64598
          (fun i1  ->
             FStar_All.pipe_left
               (fun _64605  -> FStar_Pervasives_Native.Some _64605)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____64607,(e2,uu____64609)::(e1,uu____64611)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____64634 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____64634
          (fun e11  ->
             let uu____64640 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____64640
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _64647  -> FStar_Pervasives_Native.Some _64647)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____64648 ->
        ((let uu____64650 =
            let uu____64656 =
              let uu____64658 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____64658  in
            (FStar_Errors.Warning_NotEmbedded, uu____64656)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____64650);
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