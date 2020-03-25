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
    let uu____77 =
      let uu____85 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____85, [])  in
    FStar_Syntax_Syntax.ET_app uu____77
  
let mk_emb' :
  'uu____99 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'uu____99 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'uu____99 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'uu____99 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____141 = mkFV fv [] []  in
        let uu____146 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____141 uu____146
  
let mk_lazy :
  'uu____158 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'uu____158 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____184 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____184;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk1 =
            FStar_Thunk.mk
              (fun uu____190  ->
                 let uu____191 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____191)
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
           FStar_Syntax_Syntax.ltyp = uu____236;
           FStar_Syntax_Syntax.rng = uu____237;_},uu____238)
        ->
        let uu____257 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun uu____260  -> FStar_Pervasives_Native.Some uu____260)
          uu____257
    | uu____261 ->
        ((let uu____263 =
            let uu____269 =
              let uu____271 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____271  in
            (FStar_Errors.Warning_NotEmbedded, uu____269)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____263);
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
           FStar_Syntax_Syntax.ltyp = uu____305;
           FStar_Syntax_Syntax.rng = uu____306;_},uu____307)
        ->
        let uu____326 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____326
    | uu____327 ->
        ((let uu____329 =
            let uu____335 =
              let uu____337 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____337  in
            (FStar_Errors.Warning_NotEmbedded, uu____335)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____329);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_binder unembed_binder
    FStar_Reflection_Data.fstar_refl_binder_fv
  
let (e_optionstate :
  FStar_Options.optionstate FStar_TypeChecker_NBETerm.embedding) =
  let embed_optionstate cb b =
    mk_lazy cb b FStar_Reflection_Data.fstar_refl_optionstate
      FStar_Syntax_Syntax.Lazy_optionstate
     in
  let unembed_optionstate cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_optionstate ;
           FStar_Syntax_Syntax.ltyp = uu____371;
           FStar_Syntax_Syntax.rng = uu____372;_},uu____373)
        ->
        let uu____392 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____392
    | uu____393 ->
        ((let uu____395 =
            let uu____401 =
              let uu____403 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded optionstate: %s" uu____403
               in
            (FStar_Errors.Warning_NotEmbedded, uu____401)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____395);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_optionstate unembed_optionstate
    FStar_Reflection_Data.fstar_refl_optionstate_fv
  
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
          let uu____453 = f x  in
          FStar_Util.bind_opt uu____453
            (fun x1  ->
               let uu____461 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____461
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
      | uu____531 -> FStar_Pervasives_Native.None  in
    let uu____532 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____537 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____532;
      FStar_TypeChecker_NBETerm.emb_typ = uu____537
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
        let uu____570 =
          let uu____577 =
            let uu____582 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____582  in
          [uu____577]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____570
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____634)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____651 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____651
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____656 ->
        ((let uu____658 =
            let uu____664 =
              let uu____666 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____666  in
            (FStar_Errors.Warning_NotEmbedded, uu____664)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____658);
         FStar_Pervasives_Native.None)
     in
  let uu____670 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____675 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____670
    uu____675
  
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
           FStar_Syntax_Syntax.ltyp = uu____709;
           FStar_Syntax_Syntax.rng = uu____710;_},uu____711)
        ->
        let uu____730 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____730
    | uu____731 ->
        ((let uu____733 =
            let uu____739 =
              let uu____741 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____741  in
            (FStar_Errors.Warning_NotEmbedded, uu____739)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____733);
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
           FStar_Syntax_Syntax.ltyp = uu____775;
           FStar_Syntax_Syntax.rng = uu____776;_},uu____777)
        ->
        let uu____796 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____796
    | uu____797 ->
        ((let uu____799 =
            let uu____805 =
              let uu____807 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____807  in
            (FStar_Errors.Warning_NotEmbedded, uu____805)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____799);
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
           FStar_Syntax_Syntax.ltyp = uu____841;
           FStar_Syntax_Syntax.rng = uu____842;_},uu____843)
        ->
        let uu____862 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____862
    | uu____863 ->
        ((let uu____865 =
            let uu____871 =
              let uu____873 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____873  in
            (FStar_Errors.Warning_NotEmbedded, uu____871)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____865);
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
        let uu____904 =
          let uu____911 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____911]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____904
    | FStar_Reflection_Data.C_String s ->
        let uu____926 =
          let uu____933 =
            let uu____938 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____938  in
          [uu____933]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____926
    | FStar_Reflection_Data.C_Range r ->
        let uu____949 =
          let uu____956 =
            let uu____961 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____961  in
          [uu____956]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____949
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____975 =
          let uu____982 =
            let uu____987 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____987  in
          [uu____982]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____975
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____1055)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____1072 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____1072
          (fun i1  ->
             FStar_All.pipe_left
               (fun uu____1079  -> FStar_Pervasives_Native.Some uu____1079)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____1082)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____1099 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1099
          (fun s1  ->
             FStar_All.pipe_left
               (fun uu____1110  -> FStar_Pervasives_Native.Some uu____1110)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____1113)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____1130 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____1130
          (fun r1  ->
             FStar_All.pipe_left
               (fun uu____1137  -> FStar_Pervasives_Native.Some uu____1137)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____1153)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____1170 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____1170
          (fun ns1  ->
             FStar_All.pipe_left
               (fun uu____1189  -> FStar_Pervasives_Native.Some uu____1189)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____1190 ->
        ((let uu____1192 =
            let uu____1198 =
              let uu____1200 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____1200  in
            (FStar_Errors.Warning_NotEmbedded, uu____1198)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1192);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____1211  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1224 =
            let uu____1231 =
              let uu____1236 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1236  in
            [uu____1231]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____1224
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1261 =
            let uu____1268 =
              let uu____1273 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1273  in
            let uu____1274 =
              let uu____1281 =
                let uu____1286 =
                  let uu____1287 =
                    let uu____1297 =
                      let uu____1305 = e_pattern' ()  in
                      FStar_TypeChecker_NBETerm.e_tuple2 uu____1305
                        FStar_TypeChecker_NBETerm.e_bool
                       in
                    FStar_TypeChecker_NBETerm.e_list uu____1297  in
                  FStar_TypeChecker_NBETerm.embed uu____1287 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____1286  in
              [uu____1281]  in
            uu____1268 :: uu____1274  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1261
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1334 =
            let uu____1341 =
              let uu____1346 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1346  in
            [uu____1341]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1334
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1356 =
            let uu____1363 =
              let uu____1368 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1368  in
            [uu____1363]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1356
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1379 =
            let uu____1386 =
              let uu____1391 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1391  in
            let uu____1392 =
              let uu____1399 =
                let uu____1404 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1404  in
              [uu____1399]  in
            uu____1386 :: uu____1392  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1379
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____1434)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1451 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____1451
            (fun c1  ->
               FStar_All.pipe_left
                 (fun uu____1458  -> FStar_Pervasives_Native.Some uu____1458)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____1461)::(f,uu____1463)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1484 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____1484
            (fun f1  ->
               let uu____1490 =
                 let uu____1500 =
                   let uu____1510 =
                     let uu____1518 = e_pattern' ()  in
                     FStar_TypeChecker_NBETerm.e_tuple2 uu____1518
                       FStar_TypeChecker_NBETerm.e_bool
                      in
                   FStar_TypeChecker_NBETerm.e_list uu____1510  in
                 FStar_TypeChecker_NBETerm.unembed uu____1500 cb ps  in
               FStar_Util.bind_opt uu____1490
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun uu____1552  ->
                         FStar_Pervasives_Native.Some uu____1552)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1562)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1579 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1579
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun uu____1586  -> FStar_Pervasives_Native.Some uu____1586)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1589)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1606 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1606
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun uu____1613  -> FStar_Pervasives_Native.Some uu____1613)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____1616)::(bv,uu____1618)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1639 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1639
            (fun bv1  ->
               let uu____1645 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____1645
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun uu____1652  ->
                         FStar_Pervasives_Native.Some uu____1652)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1653 ->
          ((let uu____1655 =
              let uu____1661 =
                let uu____1663 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1663
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1661)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1655);
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
    let uu____1704 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1704
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1735 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1735 e_aqualv
  
let unlazy_as_t :
  'uu____1745 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'uu____1745
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____1758;
             FStar_Syntax_Syntax.rng = uu____1759;_},uu____1760)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1779 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1817 =
            let uu____1824 =
              let uu____1829 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1829  in
            [uu____1824]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1817
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1839 =
            let uu____1846 =
              let uu____1851 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1851  in
            [uu____1846]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1839
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1861 =
            let uu____1868 =
              let uu____1873 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1873  in
            [uu____1868]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1861
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1884 =
            let uu____1891 =
              let uu____1896 =
                let uu____1897 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1897 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1896  in
            let uu____1900 =
              let uu____1907 =
                let uu____1912 =
                  let uu____1913 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1913 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1912  in
              [uu____1907]  in
            uu____1891 :: uu____1900  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1884
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1938 =
            let uu____1945 =
              let uu____1950 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1950  in
            let uu____1951 =
              let uu____1958 =
                let uu____1963 =
                  let uu____1964 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1964 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1963  in
              [uu____1958]  in
            uu____1945 :: uu____1951  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1938
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1981 =
            let uu____1988 =
              let uu____1993 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1993  in
            let uu____1994 =
              let uu____2001 =
                let uu____2006 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2006  in
              [uu____2001]  in
            uu____1988 :: uu____1994  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1981
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2020 =
            let uu____2027 =
              let uu____2032 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2032  in
            [uu____2027]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____2020
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____2043 =
            let uu____2050 =
              let uu____2055 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____2055  in
            let uu____2056 =
              let uu____2063 =
                let uu____2068 =
                  let uu____2069 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2069 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2068  in
              [uu____2063]  in
            uu____2050 :: uu____2056  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____2043
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2085 =
            let uu____2092 =
              let uu____2097 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2097  in
            [uu____2092]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____2085
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2108 =
            let uu____2115 =
              let uu____2120 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2120  in
            let uu____2121 =
              let uu____2128 =
                let uu____2133 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2133  in
              [uu____2128]  in
            uu____2115 :: uu____2121  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____2108
      | FStar_Reflection_Data.Tv_Let (r,attrs,b,t1,t2) ->
          let uu____2161 =
            let uu____2168 =
              let uu____2173 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2173  in
            let uu____2175 =
              let uu____2182 =
                let uu____2187 =
                  let uu____2188 = FStar_TypeChecker_NBETerm.e_list e_term
                     in
                  FStar_TypeChecker_NBETerm.embed uu____2188 cb attrs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2187  in
              let uu____2195 =
                let uu____2202 =
                  let uu____2207 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____2207  in
                let uu____2208 =
                  let uu____2215 =
                    let uu____2220 =
                      let uu____2221 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____2221 cb t1  in
                    FStar_TypeChecker_NBETerm.as_arg uu____2220  in
                  let uu____2224 =
                    let uu____2231 =
                      let uu____2236 =
                        let uu____2237 = e_term_aq aq  in
                        FStar_TypeChecker_NBETerm.embed uu____2237 cb t2  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2236  in
                    [uu____2231]  in
                  uu____2215 :: uu____2224  in
                uu____2202 :: uu____2208  in
              uu____2182 :: uu____2195  in
            uu____2168 :: uu____2175  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____2161
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____2270 =
            let uu____2277 =
              let uu____2282 =
                let uu____2283 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2283 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____2282  in
            let uu____2286 =
              let uu____2293 =
                let uu____2298 =
                  let uu____2299 =
                    let uu____2308 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____2308  in
                  FStar_TypeChecker_NBETerm.embed uu____2299 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2298  in
              [uu____2293]  in
            uu____2277 :: uu____2286  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2270
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____2344 =
            let uu____2351 =
              let uu____2356 =
                let uu____2357 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2357 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2356  in
            let uu____2360 =
              let uu____2367 =
                let uu____2372 =
                  let uu____2373 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2373 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2372  in
              let uu____2376 =
                let uu____2383 =
                  let uu____2388 =
                    let uu____2389 =
                      let uu____2394 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2394  in
                    FStar_TypeChecker_NBETerm.embed uu____2389 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2388  in
                [uu____2383]  in
              uu____2367 :: uu____2376  in
            uu____2351 :: uu____2360  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2344
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2422 =
            let uu____2429 =
              let uu____2434 =
                let uu____2435 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2435 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2434  in
            let uu____2438 =
              let uu____2445 =
                let uu____2450 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2450  in
              let uu____2451 =
                let uu____2458 =
                  let uu____2463 =
                    let uu____2464 =
                      let uu____2469 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2469  in
                    FStar_TypeChecker_NBETerm.embed uu____2464 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2463  in
                [uu____2458]  in
              uu____2445 :: uu____2451  in
            uu____2429 :: uu____2438  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2422
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2510,(b,uu____2512)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2531 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2531
            (fun b1  ->
               FStar_All.pipe_left
                 (fun uu____2538  -> FStar_Pervasives_Native.Some uu____2538)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2540,(b,uu____2542)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2561 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2561
            (fun b1  ->
               FStar_All.pipe_left
                 (fun uu____2568  -> FStar_Pervasives_Native.Some uu____2568)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2570,(f,uu____2572)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2591 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____2591
            (fun f1  ->
               FStar_All.pipe_left
                 (fun uu____2598  -> FStar_Pervasives_Native.Some uu____2598)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2600,(r,uu____2602)::(l,uu____2604)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2627 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____2627
            (fun l1  ->
               let uu____2633 = FStar_TypeChecker_NBETerm.unembed e_argv cb r
                  in
               FStar_Util.bind_opt uu____2633
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun uu____2640  ->
                         FStar_Pervasives_Native.Some uu____2640)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2642,(t1,uu____2644)::(b,uu____2646)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2669 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2669
            (fun b1  ->
               let uu____2675 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2675
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun uu____2682  ->
                         FStar_Pervasives_Native.Some uu____2682)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2684,(t1,uu____2686)::(b,uu____2688)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2711 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2711
            (fun b1  ->
               let uu____2717 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____2717
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun uu____2724  ->
                         FStar_Pervasives_Native.Some uu____2724)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2726,(u,uu____2728)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2747 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____2747
            (fun u1  ->
               FStar_All.pipe_left
                 (fun uu____2754  -> FStar_Pervasives_Native.Some uu____2754)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2756,(t1,uu____2758)::(b,uu____2760)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2783 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2783
            (fun b1  ->
               let uu____2789 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2789
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun uu____2796  ->
                         FStar_Pervasives_Native.Some uu____2796)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2798,(c,uu____2800)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2819 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____2819
            (fun c1  ->
               FStar_All.pipe_left
                 (fun uu____2826  -> FStar_Pervasives_Native.Some uu____2826)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2828,(l,uu____2830)::(u,uu____2832)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2855 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____2855
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun uu____2864  -> FStar_Pervasives_Native.Some uu____2864)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2866,(t2,uu____2868)::(t1,uu____2870)::(b,uu____2872)::
           (attrs,uu____2874)::(r,uu____2876)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2911 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____2911
            (fun r1  ->
               let uu____2921 =
                 let uu____2926 = FStar_TypeChecker_NBETerm.e_list e_term  in
                 FStar_TypeChecker_NBETerm.unembed uu____2926 cb attrs  in
               FStar_Util.bind_opt uu____2921
                 (fun attrs1  ->
                    let uu____2940 =
                      FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
                    FStar_Util.bind_opt uu____2940
                      (fun b1  ->
                         let uu____2946 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                         FStar_Util.bind_opt uu____2946
                           (fun t11  ->
                              let uu____2952 =
                                FStar_TypeChecker_NBETerm.unembed e_term cb
                                  t2
                                 in
                              FStar_Util.bind_opt uu____2952
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun uu____2959  ->
                                        FStar_Pervasives_Native.Some
                                          uu____2959)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, attrs1, b1, t11, t21)))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2964,(brs,uu____2966)::(t1,uu____2968)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2991 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
          FStar_Util.bind_opt uu____2991
            (fun t2  ->
               let uu____2997 =
                 let uu____3002 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____3002 cb brs  in
               FStar_Util.bind_opt uu____2997
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun uu____3017  ->
                         FStar_Pervasives_Native.Some uu____3017)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____3021,(tacopt,uu____3023)::(t1,uu____3025)::(e,uu____3027)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____3054 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____3054
            (fun e1  ->
               let uu____3060 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____3060
                 (fun t2  ->
                    let uu____3066 =
                      let uu____3071 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3071 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3066
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun uu____3086  ->
                              FStar_Pervasives_Native.Some uu____3086)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____3090,(tacopt,uu____3092)::(c,uu____3094)::(e,uu____3096)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____3123 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____3123
            (fun e1  ->
               let uu____3129 = FStar_TypeChecker_NBETerm.unembed e_comp cb c
                  in
               FStar_Util.bind_opt uu____3129
                 (fun c1  ->
                    let uu____3135 =
                      let uu____3140 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3140 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3135
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun uu____3155  ->
                              FStar_Pervasives_Native.Some uu____3155)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____3159,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun uu____3176  -> FStar_Pervasives_Native.Some uu____3176)
            FStar_Reflection_Data.Tv_Unknown
      | uu____3177 ->
          ((let uu____3179 =
              let uu____3185 =
                let uu____3187 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____3187
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3185)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3179);
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
    let uu____3214 =
      let uu____3221 =
        let uu____3226 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____3226  in
      let uu____3228 =
        let uu____3235 =
          let uu____3240 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____3240  in
        let uu____3241 =
          let uu____3248 =
            let uu____3253 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3253  in
          [uu____3248]  in
        uu____3235 :: uu____3241  in
      uu____3221 :: uu____3228  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____3214
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3286,(s,uu____3288)::(idx,uu____3290)::(nm,uu____3292)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____3319 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____3319
          (fun nm1  ->
             let uu____3329 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____3329
               (fun idx1  ->
                  let uu____3335 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____3335
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun uu____3342  ->
                            FStar_Pervasives_Native.Some uu____3342)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____3343 ->
        ((let uu____3345 =
            let uu____3351 =
              let uu____3353 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3353  in
            (FStar_Errors.Warning_NotEmbedded, uu____3351)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3345);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____3377 =
          let uu____3384 =
            let uu____3389 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3389  in
          let uu____3390 =
            let uu____3397 =
              let uu____3402 =
                let uu____3403 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____3403 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3402  in
            [uu____3397]  in
          uu____3384 :: uu____3390  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3377
    | FStar_Reflection_Data.C_GTotal (t,md) ->
        let uu____3428 =
          let uu____3435 =
            let uu____3440 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3440  in
          let uu____3441 =
            let uu____3448 =
              let uu____3453 =
                let uu____3454 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____3454 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3453  in
            [uu____3448]  in
          uu____3435 :: uu____3441  in
        mkConstruct
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.fv []
          uu____3428
    | FStar_Reflection_Data.C_Lemma (pre,post,pats) ->
        let uu____3476 =
          let uu____3483 =
            let uu____3488 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3488  in
          let uu____3489 =
            let uu____3496 =
              let uu____3501 = FStar_TypeChecker_NBETerm.embed e_term cb post
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3501  in
            let uu____3502 =
              let uu____3509 =
                let uu____3514 =
                  FStar_TypeChecker_NBETerm.embed e_term cb pats  in
                FStar_TypeChecker_NBETerm.as_arg uu____3514  in
              [uu____3509]  in
            uu____3496 :: uu____3502  in
          uu____3483 :: uu____3489  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3476
    | FStar_Reflection_Data.C_Eff (us,eff,res,args) ->
        let uu____3543 =
          let uu____3550 =
            let uu____3555 =
              let uu____3556 =
                FStar_TypeChecker_NBETerm.e_list
                  FStar_TypeChecker_NBETerm.e_unit
                 in
              FStar_TypeChecker_NBETerm.embed uu____3556 cb us  in
            FStar_TypeChecker_NBETerm.as_arg uu____3555  in
          let uu____3563 =
            let uu____3570 =
              let uu____3575 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_string_list cb eff
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3575  in
            let uu____3579 =
              let uu____3586 =
                let uu____3591 =
                  FStar_TypeChecker_NBETerm.embed e_term cb res  in
                FStar_TypeChecker_NBETerm.as_arg uu____3591  in
              let uu____3592 =
                let uu____3599 =
                  let uu____3604 =
                    let uu____3605 = FStar_TypeChecker_NBETerm.e_list e_argv
                       in
                    FStar_TypeChecker_NBETerm.embed uu____3605 cb args  in
                  FStar_TypeChecker_NBETerm.as_arg uu____3604  in
                [uu____3599]  in
              uu____3586 :: uu____3592  in
            uu____3570 :: uu____3579  in
          uu____3550 :: uu____3563  in
        mkConstruct FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.fv
          [] uu____3543
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3648,(md,uu____3650)::(t1,uu____3652)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3675 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3675
          (fun t2  ->
             let uu____3681 =
               let uu____3686 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3686 cb md  in
             FStar_Util.bind_opt uu____3681
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun uu____3701  ->
                       FStar_Pervasives_Native.Some uu____3701)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3705,(md,uu____3707)::(t1,uu____3709)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
        ->
        let uu____3732 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3732
          (fun t2  ->
             let uu____3738 =
               let uu____3743 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3743 cb md  in
             FStar_Util.bind_opt uu____3738
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun uu____3758  ->
                       FStar_Pervasives_Native.Some uu____3758)
                    (FStar_Reflection_Data.C_GTotal (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3762,(post,uu____3764)::(pre,uu____3766)::(pats,uu____3768)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3795 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____3795
          (fun pre1  ->
             let uu____3801 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____3801
               (fun post1  ->
                  let uu____3807 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb pats  in
                  FStar_Util.bind_opt uu____3807
                    (fun pats1  ->
                       FStar_All.pipe_left
                         (fun uu____3814  ->
                            FStar_Pervasives_Native.Some uu____3814)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1, pats1)))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3816,(args,uu____3818)::(res,uu____3820)::(eff,uu____3822)::
         (us,uu____3824)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
        ->
        let uu____3855 =
          let uu____3860 =
            FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_unit
             in
          FStar_TypeChecker_NBETerm.unembed uu____3860 cb us  in
        FStar_Util.bind_opt uu____3855
          (fun us1  ->
             let uu____3874 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_string_list cb eff
                in
             FStar_Util.bind_opt uu____3874
               (fun eff1  ->
                  let uu____3892 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb res  in
                  FStar_Util.bind_opt uu____3892
                    (fun res1  ->
                       let uu____3898 =
                         let uu____3903 =
                           FStar_TypeChecker_NBETerm.e_list e_argv  in
                         FStar_TypeChecker_NBETerm.unembed uu____3903 cb args
                          in
                       FStar_Util.bind_opt uu____3898
                         (fun args1  ->
                            FStar_All.pipe_left
                              (fun uu____3918  ->
                                 FStar_Pervasives_Native.Some uu____3918)
                              (FStar_Reflection_Data.C_Eff
                                 (us1, eff1, res1, args1))))))
    | uu____3923 ->
        ((let uu____3925 =
            let uu____3931 =
              let uu____3933 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3933
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3931)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3925);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3979,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3995,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4011,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____4026 ->
        ((let uu____4028 =
            let uu____4034 =
              let uu____4036 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____4036  in
            (FStar_Errors.Warning_NotEmbedded, uu____4034)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4028);
         FStar_Pervasives_Native.None)
     in
  let uu____4040 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____4040 
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
           FStar_Syntax_Syntax.ltyp = uu____4071;
           FStar_Syntax_Syntax.rng = uu____4072;_},uu____4073)
        ->
        let uu____4092 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4092
    | uu____4093 ->
        ((let uu____4095 =
            let uu____4101 =
              let uu____4103 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____4103  in
            (FStar_Errors.Warning_NotEmbedded, uu____4101)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4095);
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
    let uu____4132 =
      let uu____4138 = FStar_Ident.range_of_id i  in
      let uu____4139 = FStar_Ident.text_of_id i  in (uu____4138, uu____4139)
       in
    FStar_TypeChecker_NBETerm.embed repr cb uu____4132  in
  let unembed_ident cb t =
    let uu____4162 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____4162 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4186 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4186
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
    let uu____4196 =
      let uu____4204 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____4206 =
        let uu____4209 = fv_as_emb_typ range_fv  in
        let uu____4210 =
          let uu____4213 = fv_as_emb_typ string_fv  in [uu____4213]  in
        uu____4209 :: uu____4210  in
      (uu____4204, uu____4206)  in
    FStar_Syntax_Syntax.ET_app uu____4196  in
  let uu____4217 =
    let uu____4218 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____4219 =
      let uu____4226 =
        let uu____4231 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____4231  in
      let uu____4236 =
        let uu____4243 =
          let uu____4248 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____4248  in
        [uu____4243]  in
      uu____4226 :: uu____4236  in
    mkFV uu____4218 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____4219
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____4217 et 
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
        let uu____4305 =
          let uu____4312 =
            let uu____4317 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____4317  in
          let uu____4319 =
            let uu____4326 =
              let uu____4331 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____4331  in
            let uu____4332 =
              let uu____4339 =
                let uu____4344 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____4344  in
              let uu____4347 =
                let uu____4354 =
                  let uu____4359 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4359  in
                let uu____4360 =
                  let uu____4367 =
                    let uu____4372 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4372  in
                  [uu____4367]  in
                uu____4354 :: uu____4360  in
              uu____4339 :: uu____4347  in
            uu____4326 :: uu____4332  in
          uu____4312 :: uu____4319  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____4305
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4399 =
          let uu____4406 =
            let uu____4411 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4411  in
          let uu____4415 =
            let uu____4422 =
              let uu____4427 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____4427  in
            [uu____4422]  in
          uu____4406 :: uu____4415  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____4399
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____4457 =
          let uu____4464 =
            let uu____4469 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4469  in
          let uu____4473 =
            let uu____4480 =
              let uu____4485 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____4485  in
            let uu____4488 =
              let uu____4495 =
                let uu____4500 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____4500  in
              let uu____4501 =
                let uu____4508 =
                  let uu____4513 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4513  in
                let uu____4514 =
                  let uu____4521 =
                    let uu____4526 =
                      let uu____4527 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____4527 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4526  in
                  [uu____4521]  in
                uu____4508 :: uu____4514  in
              uu____4495 :: uu____4501  in
            uu____4480 :: uu____4488  in
          uu____4464 :: uu____4473  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____4457
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4587,(dcs,uu____4589)::(t1,uu____4591)::(bs,uu____4593)::
         (us,uu____4595)::(nm,uu____4597)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____4632 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____4632
          (fun nm1  ->
             let uu____4650 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____4650
               (fun us1  ->
                  let uu____4664 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____4664
                    (fun bs1  ->
                       let uu____4670 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____4670
                         (fun t2  ->
                            let uu____4676 =
                              let uu____4684 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____4684 cb
                                dcs
                               in
                            FStar_Util.bind_opt uu____4676
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun uu____4714  ->
                                      FStar_Pervasives_Native.Some uu____4714)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4722,(t1,uu____4724)::(ty,uu____4726)::(univs1,uu____4728)::
         (fvar1,uu____4730)::(r,uu____4732)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____4767 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____4767
          (fun r1  ->
             let uu____4777 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1
                in
             FStar_Util.bind_opt uu____4777
               (fun fvar2  ->
                  let uu____4783 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____4783
                    (fun univs2  ->
                       let uu____4797 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____4797
                         (fun ty1  ->
                            let uu____4803 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____4803
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun uu____4810  ->
                                      FStar_Pervasives_Native.Some uu____4810)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4815,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4830 ->
        ((let uu____4832 =
            let uu____4838 =
              let uu____4840 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4840
               in
            (FStar_Errors.Warning_NotEmbedded, uu____4838)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4832);
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
        let uu____4863 =
          let uu____4870 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____4870]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4863
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____4885 =
          let uu____4892 =
            let uu____4897 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4897  in
          let uu____4898 =
            let uu____4905 =
              let uu____4910 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4910  in
            [uu____4905]  in
          uu____4892 :: uu____4898  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4885
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4939,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4955,(i,uu____4957)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____4976 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____4976
          (fun i1  ->
             FStar_All.pipe_left
               (fun uu____4983  -> FStar_Pervasives_Native.Some uu____4983)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4985,(e2,uu____4987)::(e1,uu____4989)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____5012 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____5012
          (fun e11  ->
             let uu____5018 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____5018
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun uu____5025  ->
                       FStar_Pervasives_Native.Some uu____5025)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____5026 ->
        ((let uu____5028 =
            let uu____5034 =
              let uu____5036 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____5036  in
            (FStar_Errors.Warning_NotEmbedded, uu____5034)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5028);
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
let (e_lid : FStar_Ident.lid FStar_TypeChecker_NBETerm.embedding) =
  let embed1 rng lid =
    let uu____5065 = FStar_Ident.path_of_lid lid  in
    FStar_TypeChecker_NBETerm.embed e_string_list rng uu____5065  in
  let unembed1 cb t =
    let uu____5087 = FStar_TypeChecker_NBETerm.unembed e_string_list cb t  in
    FStar_Util.map_opt uu____5087
      (fun p  -> FStar_Ident.lid_of_path p FStar_Range.dummyRange)
     in
  let uu____5104 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____5109 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed1 unembed1 uu____5104 uu____5109 
let (e_qualifier :
  FStar_Reflection_Data.qualifier FStar_TypeChecker_NBETerm.embedding) =
  let embed1 cb q =
    match q with
    | FStar_Reflection_Data.Assumption  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.New  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Private  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.fv []
          []
    | FStar_Reflection_Data.Unfold_for_unification_and_vcgen  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Visible_default  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Irreducible  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Abstract  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Abstract.FStar_Reflection_Data.fv []
          []
    | FStar_Reflection_Data.Inline_for_extraction  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.NoExtract  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Noeq  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Unopteq  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.fv []
          []
    | FStar_Reflection_Data.TotalEffect  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Logic  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Reifiable  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.ExceptionConstructor  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.HasMaskedEffect  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Effect  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.fv []
          []
    | FStar_Reflection_Data.OnlyName  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.fv []
          []
    | FStar_Reflection_Data.Reflectable l ->
        let uu____5197 =
          let uu____5204 =
            let uu____5209 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____5209  in
          [uu____5204]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.fv
          [] uu____5197
    | FStar_Reflection_Data.Discriminator l ->
        let uu____5219 =
          let uu____5226 =
            let uu____5231 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____5231  in
          [uu____5226]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.fv
          [] uu____5219
    | FStar_Reflection_Data.Action l ->
        let uu____5241 =
          let uu____5248 =
            let uu____5253 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____5253  in
          [uu____5248]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.fv []
          uu____5241
    | FStar_Reflection_Data.Projector (l,i) ->
        let uu____5264 =
          let uu____5271 =
            let uu____5276 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____5276  in
          let uu____5277 =
            let uu____5284 =
              let uu____5289 = FStar_TypeChecker_NBETerm.embed e_ident cb i
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____5289  in
            [uu____5284]  in
          uu____5271 :: uu____5277  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.fv
          [] uu____5264
    | FStar_Reflection_Data.RecordType (ids1,ids2) ->
        let uu____5312 =
          let uu____5319 =
            let uu____5324 =
              let uu____5325 = FStar_TypeChecker_NBETerm.e_list e_ident  in
              FStar_TypeChecker_NBETerm.embed uu____5325 cb ids1  in
            FStar_TypeChecker_NBETerm.as_arg uu____5324  in
          let uu____5332 =
            let uu____5339 =
              let uu____5344 =
                let uu____5345 = FStar_TypeChecker_NBETerm.e_list e_ident  in
                FStar_TypeChecker_NBETerm.embed uu____5345 cb ids2  in
              FStar_TypeChecker_NBETerm.as_arg uu____5344  in
            [uu____5339]  in
          uu____5319 :: uu____5332  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.fv
          [] uu____5312
    | FStar_Reflection_Data.RecordConstructor (ids1,ids2) ->
        let uu____5374 =
          let uu____5381 =
            let uu____5386 =
              let uu____5387 = FStar_TypeChecker_NBETerm.e_list e_ident  in
              FStar_TypeChecker_NBETerm.embed uu____5387 cb ids1  in
            FStar_TypeChecker_NBETerm.as_arg uu____5386  in
          let uu____5394 =
            let uu____5401 =
              let uu____5406 =
                let uu____5407 = FStar_TypeChecker_NBETerm.e_list e_ident  in
                FStar_TypeChecker_NBETerm.embed uu____5407 cb ids2  in
              FStar_TypeChecker_NBETerm.as_arg uu____5406  in
            [uu____5401]  in
          uu____5381 :: uu____5394  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.fv
          [] uu____5374
     in
  let unembed1 cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Assumption
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.New
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Private
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.lid
        ->
        FStar_Pervasives_Native.Some
          FStar_Reflection_Data.Unfold_for_unification_and_vcgen
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Visible_default
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Irreducible
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Abstract.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Abstract
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.lid
        ->
        FStar_Pervasives_Native.Some
          FStar_Reflection_Data.Inline_for_extraction
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.NoExtract
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Noeq
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unopteq
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.TotalEffect
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Logic
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Reifiable
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.lid
        ->
        FStar_Pervasives_Native.Some
          FStar_Reflection_Data.ExceptionConstructor
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.HasMaskedEffect
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Effect
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.OnlyName
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5677)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
        ->
        let uu____5694 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5694
          (fun l1  ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Reflectable l1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5701)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
        ->
        let uu____5718 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5718
          (fun l1  ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Discriminator l1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5725)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
        ->
        let uu____5742 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5742
          (fun l1  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Action l1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,[],(i,uu____5749)::(l,uu____5751)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
        ->
        let uu____5772 = FStar_TypeChecker_NBETerm.unembed e_ident cb i  in
        FStar_Util.bind_opt uu____5772
          (fun i1  ->
             let uu____5778 = FStar_TypeChecker_NBETerm.unembed e_lid cb l
                in
             FStar_Util.bind_opt uu____5778
               (fun l1  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Projector (l1, i1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,[],(ids2,uu____5785)::(ids1,uu____5787)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
        ->
        let uu____5808 =
          let uu____5813 = FStar_TypeChecker_NBETerm.e_list e_ident  in
          FStar_TypeChecker_NBETerm.unembed uu____5813 cb ids1  in
        FStar_Util.bind_opt uu____5808
          (fun ids11  ->
             let uu____5827 =
               let uu____5832 = FStar_TypeChecker_NBETerm.e_list e_ident  in
               FStar_TypeChecker_NBETerm.unembed uu____5832 cb ids2  in
             FStar_Util.bind_opt uu____5827
               (fun ids21  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordType (ids11, ids21))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,[],(ids2,uu____5851)::(ids1,uu____5853)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
        ->
        let uu____5874 =
          let uu____5879 = FStar_TypeChecker_NBETerm.e_list e_ident  in
          FStar_TypeChecker_NBETerm.unembed uu____5879 cb ids1  in
        FStar_Util.bind_opt uu____5874
          (fun ids11  ->
             let uu____5893 =
               let uu____5898 = FStar_TypeChecker_NBETerm.e_list e_ident  in
               FStar_TypeChecker_NBETerm.unembed uu____5898 cb ids2  in
             FStar_Util.bind_opt uu____5893
               (fun ids21  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordConstructor (ids11, ids21))))
    | uu____5915 ->
        ((let uu____5917 =
            let uu____5923 =
              let uu____5925 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded qualifier: %s" uu____5925
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5923)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5917);
         FStar_Pervasives_Native.None)
     in
  let uu____5929 =
    mkConstruct FStar_Reflection_Data.fstar_refl_qualifier_fv [] []  in
  let uu____5934 =
    fv_as_emb_typ FStar_Reflection_Data.fstar_refl_qualifier_fv  in
  FStar_TypeChecker_NBETerm.mk_emb embed1 unembed1 uu____5929 uu____5934 
let (e_qualifiers :
  FStar_Reflection_Data.qualifier Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_qualifier 