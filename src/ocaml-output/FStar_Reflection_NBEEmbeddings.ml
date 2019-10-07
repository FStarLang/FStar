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
  'Auu____99 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____99 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____99 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____99 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____141 = mkFV fv [] []  in
        let uu____146 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____141 uu____146
  
let mk_lazy :
  'Auu____158 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____158 ->
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
            FStar_Common.mk_thunk
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
        FStar_All.pipe_left (fun _260  -> FStar_Pervasives_Native.Some _260)
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
               (fun _1079  -> FStar_Pervasives_Native.Some _1079)
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
               (fun _1110  -> FStar_Pervasives_Native.Some _1110)
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
               (fun _1137  -> FStar_Pervasives_Native.Some _1137)
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
               (fun _1189  -> FStar_Pervasives_Native.Some _1189)
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
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____1251 =
            let uu____1258 =
              let uu____1263 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1263  in
            let uu____1264 =
              let uu____1271 =
                let uu____1276 =
                  let uu____1277 =
                    let uu____1282 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____1282  in
                  FStar_TypeChecker_NBETerm.embed uu____1277 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____1276  in
              [uu____1271]  in
            uu____1258 :: uu____1264  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1251
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1300 =
            let uu____1307 =
              let uu____1312 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1312  in
            [uu____1307]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1300
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1322 =
            let uu____1329 =
              let uu____1334 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1334  in
            [uu____1329]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1322
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1345 =
            let uu____1352 =
              let uu____1357 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1357  in
            let uu____1358 =
              let uu____1365 =
                let uu____1370 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1370  in
              [uu____1365]  in
            uu____1352 :: uu____1358  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1345
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____1400)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1417 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____1417
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _1424  -> FStar_Pervasives_Native.Some _1424)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____1427)::(f,uu____1429)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1450 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____1450
            (fun f1  ->
               let uu____1456 =
                 let uu____1461 =
                   let uu____1466 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____1466  in
                 FStar_TypeChecker_NBETerm.unembed uu____1461 cb ps  in
               FStar_Util.bind_opt uu____1456
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _1479  -> FStar_Pervasives_Native.Some _1479)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1484)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1501 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1501
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _1508  -> FStar_Pervasives_Native.Some _1508)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1511)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1528 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1528
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _1535  -> FStar_Pervasives_Native.Some _1535)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____1538)::(bv,uu____1540)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1561 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1561
            (fun bv1  ->
               let uu____1567 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____1567
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _1574  -> FStar_Pervasives_Native.Some _1574)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1575 ->
          ((let uu____1577 =
              let uu____1583 =
                let uu____1585 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1585
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1583)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1577);
=======
          let uu____1195 =
            let uu____1202 =
              let uu____1207 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1207  in
            let uu____1208 =
              let uu____1215 =
                let uu____1220 =
                  let uu____1221 =
                    let uu____1231 =
                      let uu____1239 = e_pattern' ()  in
                      FStar_TypeChecker_NBETerm.e_tuple2 uu____1239
=======
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
>>>>>>> snap
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
                 (fun _1458  -> FStar_Pervasives_Native.Some _1458)
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
                      (fun _1552  -> FStar_Pervasives_Native.Some _1552)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1562)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1579 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1579
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _1586  -> FStar_Pervasives_Native.Some _1586)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1589)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1606 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1606
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _1613  -> FStar_Pervasives_Native.Some _1613)
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
                      (fun _1652  -> FStar_Pervasives_Native.Some _1652)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1653 ->
          ((let uu____1655 =
              let uu____1661 =
                let uu____1663 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1663
                 in
<<<<<<< HEAD
              (FStar_Errors.Warning_NotEmbedded, uu____1595)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1589);
>>>>>>> snap
=======
              (FStar_Errors.Warning_NotEmbedded, uu____1661)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1655);
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____1626 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1626
=======
    let uu____1638 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1638
>>>>>>> snap
=======
    let uu____1704 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1704
>>>>>>> snap
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____1657 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1657 e_aqualv
  
let rec unlazy_as_t :
  'Auu____1667 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1667
=======
    let uu____1669 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1669 e_aqualv
=======
    let uu____1735 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1735 e_aqualv
>>>>>>> snap
  
let rec unlazy_as_t :
  'Auu____1745 .
    FStar_Syntax_Syntax.lazy_kind ->
<<<<<<< HEAD
      FStar_TypeChecker_NBETerm.t -> 'Auu____1679
>>>>>>> snap
=======
      FStar_TypeChecker_NBETerm.t -> 'Auu____1745
>>>>>>> snap
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
<<<<<<< HEAD
<<<<<<< HEAD
             FStar_Syntax_Syntax.ltyp = uu____1680;
             FStar_Syntax_Syntax.rng = uu____1681;_},uu____1682)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1701 -> failwith "Not a Lazy of the expected kind (NBE)"
=======
             FStar_Syntax_Syntax.ltyp = uu____1692;
             FStar_Syntax_Syntax.rng = uu____1693;_},uu____1694)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1713 -> failwith "Not a Lazy of the expected kind (NBE)"
>>>>>>> snap
=======
             FStar_Syntax_Syntax.ltyp = uu____1758;
             FStar_Syntax_Syntax.rng = uu____1759;_},uu____1760)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1779 -> failwith "Not a Lazy of the expected kind (NBE)"
>>>>>>> snap
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____1739 =
            let uu____1746 =
              let uu____1751 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1751  in
            [uu____1746]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1739
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1761 =
            let uu____1768 =
              let uu____1773 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1773  in
            [uu____1768]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1761
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1783 =
            let uu____1790 =
              let uu____1795 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1795  in
            [uu____1790]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1783
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1806 =
            let uu____1813 =
              let uu____1818 =
                let uu____1819 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1819 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1818  in
            let uu____1822 =
              let uu____1829 =
                let uu____1834 =
                  let uu____1835 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1835 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1834  in
              [uu____1829]  in
            uu____1813 :: uu____1822  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1806
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1860 =
            let uu____1867 =
              let uu____1872 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1872  in
            let uu____1873 =
              let uu____1880 =
                let uu____1885 =
                  let uu____1886 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1886 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1885  in
              [uu____1880]  in
            uu____1867 :: uu____1873  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1860
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1903 =
            let uu____1910 =
              let uu____1915 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1915  in
            let uu____1916 =
              let uu____1923 =
                let uu____1928 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1928  in
              [uu____1923]  in
            uu____1910 :: uu____1916  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1903
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1942 =
            let uu____1949 =
              let uu____1954 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1954  in
            [uu____1949]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1942
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____1965 =
            let uu____1972 =
              let uu____1977 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1977  in
            let uu____1978 =
              let uu____1985 =
                let uu____1990 =
                  let uu____1991 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1991 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1990  in
              [uu____1985]  in
            uu____1972 :: uu____1978  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1965
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2007 =
            let uu____2014 =
              let uu____2019 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2019  in
            [uu____2014]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____2007
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2030 =
            let uu____2037 =
              let uu____2042 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2042  in
            let uu____2043 =
              let uu____2050 =
                let uu____2055 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2055  in
              [uu____2050]  in
            uu____2037 :: uu____2043  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____2030
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2078 =
            let uu____2085 =
              let uu____2090 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2090  in
            let uu____2092 =
              let uu____2099 =
                let uu____2104 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2104  in
              let uu____2105 =
                let uu____2112 =
                  let uu____2117 =
                    let uu____2118 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____2118 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2117  in
                let uu____2121 =
                  let uu____2128 =
                    let uu____2133 =
                      let uu____2134 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____2134 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____2133  in
                  [uu____2128]  in
                uu____2112 :: uu____2121  in
              uu____2099 :: uu____2105  in
            uu____2085 :: uu____2092  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____2078
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____2163 =
            let uu____2170 =
              let uu____2175 =
                let uu____2176 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2176 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____2175  in
            let uu____2179 =
              let uu____2186 =
                let uu____2191 =
                  let uu____2192 =
                    let uu____2201 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____2201  in
                  FStar_TypeChecker_NBETerm.embed uu____2192 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2191  in
              [uu____2186]  in
            uu____2170 :: uu____2179  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2163
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____2237 =
            let uu____2244 =
              let uu____2249 =
                let uu____2250 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2250 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2249  in
            let uu____2253 =
              let uu____2260 =
                let uu____2265 =
                  let uu____2266 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2266 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2265  in
              let uu____2269 =
                let uu____2276 =
                  let uu____2281 =
                    let uu____2282 =
                      let uu____2287 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2287  in
                    FStar_TypeChecker_NBETerm.embed uu____2282 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2281  in
                [uu____2276]  in
              uu____2260 :: uu____2269  in
            uu____2244 :: uu____2253  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2237
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2315 =
            let uu____2322 =
              let uu____2327 =
                let uu____2328 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2328 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2327  in
            let uu____2331 =
              let uu____2338 =
                let uu____2343 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2343  in
              let uu____2344 =
                let uu____2351 =
                  let uu____2356 =
                    let uu____2357 =
                      let uu____2362 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2362  in
                    FStar_TypeChecker_NBETerm.embed uu____2357 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2356  in
                [uu____2351]  in
              uu____2338 :: uu____2344  in
            uu____2322 :: uu____2331  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2315
=======
          let uu____1751 =
            let uu____1758 =
              let uu____1763 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1763  in
            [uu____1758]  in
=======
          let uu____1817 =
            let uu____1824 =
              let uu____1829 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1829  in
            [uu____1824]  in
>>>>>>> snap
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
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2156 =
            let uu____2163 =
              let uu____2168 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2168  in
            let uu____2170 =
              let uu____2177 =
                let uu____2182 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2182  in
              let uu____2183 =
                let uu____2190 =
                  let uu____2195 =
                    let uu____2196 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____2196 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2195  in
                let uu____2199 =
                  let uu____2206 =
                    let uu____2211 =
                      let uu____2212 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____2212 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____2211  in
                  [uu____2206]  in
                uu____2190 :: uu____2199  in
              uu____2177 :: uu____2183  in
            uu____2163 :: uu____2170  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____2156
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____2241 =
            let uu____2248 =
              let uu____2253 =
                let uu____2254 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2254 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____2253  in
            let uu____2257 =
              let uu____2264 =
                let uu____2269 =
                  let uu____2270 =
                    let uu____2279 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____2279  in
                  FStar_TypeChecker_NBETerm.embed uu____2270 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2269  in
              [uu____2264]  in
            uu____2248 :: uu____2257  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2241
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____2315 =
            let uu____2322 =
              let uu____2327 =
                let uu____2328 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2328 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2327  in
            let uu____2331 =
              let uu____2338 =
                let uu____2343 =
                  let uu____2344 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2344 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2343  in
              let uu____2347 =
                let uu____2354 =
                  let uu____2359 =
                    let uu____2360 =
                      let uu____2365 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2365  in
                    FStar_TypeChecker_NBETerm.embed uu____2360 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2359  in
                [uu____2354]  in
              uu____2338 :: uu____2347  in
            uu____2322 :: uu____2331  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2315
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2393 =
            let uu____2400 =
              let uu____2405 =
                let uu____2406 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2406 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2405  in
            let uu____2409 =
              let uu____2416 =
                let uu____2421 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2421  in
              let uu____2422 =
                let uu____2429 =
                  let uu____2434 =
                    let uu____2435 =
                      let uu____2440 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2440  in
                    FStar_TypeChecker_NBETerm.embed uu____2435 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2434  in
                [uu____2429]  in
              uu____2416 :: uu____2422  in
            uu____2400 :: uu____2409  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
<<<<<<< HEAD
            uu____2327
>>>>>>> snap
=======
            uu____2393
>>>>>>> snap
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
<<<<<<< HEAD
          (fv,uu____2403,(b,uu____2405)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2424 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2424
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _2431  -> FStar_Pervasives_Native.Some _2431)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2433,(b,uu____2435)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2454 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2454
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _2461  -> FStar_Pervasives_Native.Some _2461)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2463,(f,uu____2465)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2484 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____2484
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _2491  -> FStar_Pervasives_Native.Some _2491)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2493,(r,uu____2495)::(l,uu____2497)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2520 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____2520
            (fun l1  ->
               let uu____2526 = FStar_TypeChecker_NBETerm.unembed e_argv cb r
                  in
               FStar_Util.bind_opt uu____2526
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _2533  -> FStar_Pervasives_Native.Some _2533)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2535,(t1,uu____2537)::(b,uu____2539)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2562 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2562
            (fun b1  ->
               let uu____2568 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2568
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _2575  -> FStar_Pervasives_Native.Some _2575)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2577,(t1,uu____2579)::(b,uu____2581)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2604 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2604
            (fun b1  ->
               let uu____2610 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____2610
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _2617  -> FStar_Pervasives_Native.Some _2617)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2619,(u,uu____2621)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2640 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____2640
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _2647  -> FStar_Pervasives_Native.Some _2647)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2649,(t1,uu____2651)::(b,uu____2653)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2676 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2676
            (fun b1  ->
               let uu____2682 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2682
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _2689  -> FStar_Pervasives_Native.Some _2689)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2691,(c,uu____2693)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2712 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____2712
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _2719  -> FStar_Pervasives_Native.Some _2719)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2721,(l,uu____2723)::(u,uu____2725)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2748 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____2748
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _2757  -> FStar_Pervasives_Native.Some _2757)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2759,(t2,uu____2761)::(t1,uu____2763)::(b,uu____2765)::
           (r,uu____2767)::[])
=======
          (fv,uu____2415,(b,uu____2417)::[]) when
=======
          (fv,uu____2481,(b,uu____2483)::[]) when
>>>>>>> snap
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2502 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2502
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _2509  -> FStar_Pervasives_Native.Some _2509)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2511,(b,uu____2513)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2532 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2532
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _2539  -> FStar_Pervasives_Native.Some _2539)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2541,(f,uu____2543)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2562 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____2562
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _2569  -> FStar_Pervasives_Native.Some _2569)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2571,(r,uu____2573)::(l,uu____2575)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2598 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____2598
            (fun l1  ->
               let uu____2604 = FStar_TypeChecker_NBETerm.unembed e_argv cb r
                  in
               FStar_Util.bind_opt uu____2604
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _2611  -> FStar_Pervasives_Native.Some _2611)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2613,(t1,uu____2615)::(b,uu____2617)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2640 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2640
            (fun b1  ->
               let uu____2646 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2646
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _2653  -> FStar_Pervasives_Native.Some _2653)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2655,(t1,uu____2657)::(b,uu____2659)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2682 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2682
            (fun b1  ->
               let uu____2688 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____2688
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _2695  -> FStar_Pervasives_Native.Some _2695)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2697,(u,uu____2699)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2718 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____2718
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _2725  -> FStar_Pervasives_Native.Some _2725)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2727,(t1,uu____2729)::(b,uu____2731)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2754 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2754
            (fun b1  ->
               let uu____2760 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2760
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _2767  -> FStar_Pervasives_Native.Some _2767)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2769,(c,uu____2771)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2790 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____2790
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _2797  -> FStar_Pervasives_Native.Some _2797)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2799,(l,uu____2801)::(u,uu____2803)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2826 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____2826
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _2835  -> FStar_Pervasives_Native.Some _2835)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
          (fv,uu____2771,(t2,uu____2773)::(t1,uu____2775)::(b,uu____2777)::
           (r,uu____2779)::[])
>>>>>>> snap
=======
          (fv,uu____2837,(t2,uu____2839)::(t1,uu____2841)::(b,uu____2843)::
           (r,uu____2845)::[])
>>>>>>> snap
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____2798 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____2798
            (fun r1  ->
               let uu____2808 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____2808
                 (fun b1  ->
                    let uu____2814 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____2814
                      (fun t11  ->
                         let uu____2820 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____2820
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _2827  ->
                                   FStar_Pervasives_Native.Some _2827)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2830,(brs,uu____2832)::(t1,uu____2834)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2857 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
          FStar_Util.bind_opt uu____2857
            (fun t2  ->
               let uu____2863 =
                 let uu____2868 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2868 cb brs  in
               FStar_Util.bind_opt uu____2863
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _2883  -> FStar_Pervasives_Native.Some _2883)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2887,(tacopt,uu____2889)::(t1,uu____2891)::(e,uu____2893)::[])
=======
          let uu____2810 =
=======
          let uu____2876 =
>>>>>>> snap
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____2876
            (fun r1  ->
               let uu____2886 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____2886
                 (fun b1  ->
                    let uu____2892 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____2892
                      (fun t11  ->
                         let uu____2898 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____2898
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _2905  ->
                                   FStar_Pervasives_Native.Some _2905)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2908,(brs,uu____2910)::(t1,uu____2912)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2935 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
          FStar_Util.bind_opt uu____2935
            (fun t2  ->
               let uu____2941 =
                 let uu____2946 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2946 cb brs  in
               FStar_Util.bind_opt uu____2941
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _2961  -> FStar_Pervasives_Native.Some _2961)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
          (fv,uu____2899,(tacopt,uu____2901)::(t1,uu____2903)::(e,uu____2905)::[])
>>>>>>> snap
=======
          (fv,uu____2965,(tacopt,uu____2967)::(t1,uu____2969)::(e,uu____2971)::[])
>>>>>>> snap
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____2920 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____2920
            (fun e1  ->
               let uu____2926 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2926
                 (fun t2  ->
                    let uu____2932 =
                      let uu____2937 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2937 cb tacopt
                       in
                    FStar_Util.bind_opt uu____2932
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _2952  -> FStar_Pervasives_Native.Some _2952)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2956,(tacopt,uu____2958)::(c,uu____2960)::(e,uu____2962)::[])
=======
          let uu____2932 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____2932
=======
          let uu____2998 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____2998
>>>>>>> snap
            (fun e1  ->
               let uu____3004 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____3004
                 (fun t2  ->
                    let uu____3010 =
                      let uu____3015 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3015 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3010
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _3030  -> FStar_Pervasives_Native.Some _3030)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
          (fv,uu____2968,(tacopt,uu____2970)::(c,uu____2972)::(e,uu____2974)::[])
>>>>>>> snap
=======
          (fv,uu____3034,(tacopt,uu____3036)::(c,uu____3038)::(e,uu____3040)::[])
>>>>>>> snap
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____2989 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____2989
            (fun e1  ->
               let uu____2995 = FStar_TypeChecker_NBETerm.unembed e_comp cb c
                  in
               FStar_Util.bind_opt uu____2995
                 (fun c1  ->
                    let uu____3001 =
                      let uu____3006 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3006 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3001
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _3021  -> FStar_Pervasives_Native.Some _3021)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____3025,[]) when
=======
          let uu____3001 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____3001
=======
          let uu____3067 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____3067
>>>>>>> snap
            (fun e1  ->
               let uu____3073 = FStar_TypeChecker_NBETerm.unembed e_comp cb c
                  in
               FStar_Util.bind_opt uu____3073
                 (fun c1  ->
                    let uu____3079 =
                      let uu____3084 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3084 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3079
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _3099  -> FStar_Pervasives_Native.Some _3099)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
<<<<<<< HEAD
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____3037,[]) when
>>>>>>> snap
=======
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____3103,[]) when
>>>>>>> snap
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
<<<<<<< HEAD
<<<<<<< HEAD
            (fun _3042  -> FStar_Pervasives_Native.Some _3042)
            FStar_Reflection_Data.Tv_Unknown
      | uu____3043 ->
          ((let uu____3045 =
              let uu____3051 =
                let uu____3053 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____3053
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3051)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3045);
=======
            (fun _3054  -> FStar_Pervasives_Native.Some _3054)
=======
            (fun _3120  -> FStar_Pervasives_Native.Some _3120)
>>>>>>> snap
            FStar_Reflection_Data.Tv_Unknown
      | uu____3121 ->
          ((let uu____3123 =
              let uu____3129 =
                let uu____3131 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____3131
                 in
<<<<<<< HEAD
              (FStar_Errors.Warning_NotEmbedded, uu____3063)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3057);
>>>>>>> snap
=======
              (FStar_Errors.Warning_NotEmbedded, uu____3129)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3123);
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____3080 =
      let uu____3087 =
        let uu____3092 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____3092  in
      let uu____3094 =
        let uu____3101 =
          let uu____3106 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____3106  in
        let uu____3107 =
          let uu____3114 =
            let uu____3119 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3119  in
          [uu____3114]  in
        uu____3101 :: uu____3107  in
      uu____3087 :: uu____3094  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____3080
=======
    let uu____3092 =
      let uu____3099 =
        let uu____3104 =
=======
    let uu____3158 =
      let uu____3165 =
        let uu____3170 =
>>>>>>> snap
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____3170  in
      let uu____3172 =
        let uu____3179 =
          let uu____3184 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____3184  in
        let uu____3185 =
          let uu____3192 =
            let uu____3197 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3197  in
          [uu____3192]  in
        uu____3179 :: uu____3185  in
      uu____3165 :: uu____3172  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
<<<<<<< HEAD
      uu____3092
>>>>>>> snap
=======
      uu____3158
>>>>>>> snap
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
<<<<<<< HEAD
        (fv,uu____3152,(s,uu____3154)::(idx,uu____3156)::(nm,uu____3158)::[])
=======
        (fv,uu____3164,(s,uu____3166)::(idx,uu____3168)::(nm,uu____3170)::[])
>>>>>>> snap
=======
        (fv,uu____3230,(s,uu____3232)::(idx,uu____3234)::(nm,uu____3236)::[])
>>>>>>> snap
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____3185 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____3185
          (fun nm1  ->
             let uu____3195 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____3195
               (fun idx1  ->
                  let uu____3201 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____3201
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _3208  -> FStar_Pervasives_Native.Some _3208)
=======
        let uu____3197 =
=======
        let uu____3263 =
>>>>>>> snap
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____3263
          (fun nm1  ->
             let uu____3273 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____3273
               (fun idx1  ->
                  let uu____3279 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____3279
                    (fun s1  ->
                       FStar_All.pipe_left
<<<<<<< HEAD
                         (fun _3220  -> FStar_Pervasives_Native.Some _3220)
>>>>>>> snap
=======
                         (fun _3286  -> FStar_Pervasives_Native.Some _3286)
>>>>>>> snap
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____3209 ->
        ((let uu____3211 =
            let uu____3217 =
              let uu____3219 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3219  in
            (FStar_Errors.Warning_NotEmbedded, uu____3217)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3211);
=======
    | uu____3221 ->
        ((let uu____3223 =
            let uu____3229 =
              let uu____3231 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3231  in
            (FStar_Errors.Warning_NotEmbedded, uu____3229)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3223);
>>>>>>> snap
=======
    | uu____3287 ->
        ((let uu____3289 =
            let uu____3295 =
              let uu____3297 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3297  in
            (FStar_Errors.Warning_NotEmbedded, uu____3295)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3289);
>>>>>>> snap
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____3243 =
          let uu____3250 =
            let uu____3255 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3255  in
          let uu____3256 =
            let uu____3263 =
              let uu____3268 =
                let uu____3269 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____3269 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3268  in
            [uu____3263]  in
          uu____3250 :: uu____3256  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3243
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3293 =
          let uu____3300 =
            let uu____3305 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3305  in
          let uu____3306 =
            let uu____3313 =
              let uu____3318 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3318  in
            [uu____3313]  in
          uu____3300 :: uu____3306  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3293
=======
        let uu____3255 =
          let uu____3262 =
            let uu____3267 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3267  in
          let uu____3268 =
            let uu____3275 =
              let uu____3280 =
                let uu____3281 = FStar_TypeChecker_NBETerm.e_option e_term
=======
        let uu____3321 =
          let uu____3328 =
            let uu____3333 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3333  in
          let uu____3334 =
            let uu____3341 =
              let uu____3346 =
                let uu____3347 = FStar_TypeChecker_NBETerm.e_option e_term
>>>>>>> snap
                   in
                FStar_TypeChecker_NBETerm.embed uu____3347 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3346  in
            [uu____3341]  in
          uu____3328 :: uu____3334  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3321
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3371 =
          let uu____3378 =
            let uu____3383 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3383  in
          let uu____3384 =
            let uu____3391 =
              let uu____3396 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3396  in
            [uu____3391]  in
          uu____3378 :: uu____3384  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
<<<<<<< HEAD
          uu____3305
>>>>>>> snap
=======
          uu____3371
>>>>>>> snap
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
<<<<<<< HEAD
        (fv,uu____3351,(md,uu____3353)::(t1,uu____3355)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3378 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3378
          (fun t2  ->
             let uu____3384 =
               let uu____3389 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3389 cb md  in
             FStar_Util.bind_opt uu____3384
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _3404  -> FStar_Pervasives_Native.Some _3404)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3408,(post,uu____3410)::(pre,uu____3412)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3435 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____3435
          (fun pre1  ->
             let uu____3441 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____3441
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _3448  -> FStar_Pervasives_Native.Some _3448)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3450,[]) when
=======
        (fv,uu____3363,(md,uu____3365)::(t1,uu____3367)::[]) when
=======
        (fv,uu____3429,(md,uu____3431)::(t1,uu____3433)::[]) when
>>>>>>> snap
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3456 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3456
          (fun t2  ->
             let uu____3462 =
               let uu____3467 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3467 cb md  in
             FStar_Util.bind_opt uu____3462
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _3482  -> FStar_Pervasives_Native.Some _3482)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3486,(post,uu____3488)::(pre,uu____3490)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3513 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____3513
          (fun pre1  ->
             let uu____3519 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____3519
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _3526  -> FStar_Pervasives_Native.Some _3526)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
<<<<<<< HEAD
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3462,[]) when
>>>>>>> snap
=======
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3528,[]) when
>>>>>>> snap
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
<<<<<<< HEAD
<<<<<<< HEAD
          (fun _3467  -> FStar_Pervasives_Native.Some _3467)
          FStar_Reflection_Data.C_Unknown
    | uu____3468 ->
        ((let uu____3470 =
            let uu____3476 =
              let uu____3478 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3478
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3476)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3470);
=======
          (fun _3479  -> FStar_Pervasives_Native.Some _3479)
=======
          (fun _3545  -> FStar_Pervasives_Native.Some _3545)
>>>>>>> snap
          FStar_Reflection_Data.C_Unknown
    | uu____3546 ->
        ((let uu____3548 =
            let uu____3554 =
              let uu____3556 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3556
               in
<<<<<<< HEAD
            (FStar_Errors.Warning_NotEmbedded, uu____3488)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3482);
>>>>>>> snap
=======
            (FStar_Errors.Warning_NotEmbedded, uu____3554)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3548);
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3524,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3540,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3556,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____3571 ->
        ((let uu____3573 =
            let uu____3579 =
              let uu____3581 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____3581  in
            (FStar_Errors.Warning_NotEmbedded, uu____3579)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3573);
         FStar_Pervasives_Native.None)
     in
  let uu____3585 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____3585 
=======
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3536,[]) when
=======
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3602,[]) when
>>>>>>> snap
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3618,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3634,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____3649 ->
        ((let uu____3651 =
            let uu____3657 =
              let uu____3659 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____3659  in
            (FStar_Errors.Warning_NotEmbedded, uu____3657)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3651);
         FStar_Pervasives_Native.None)
     in
  let uu____3663 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
<<<<<<< HEAD
  mk_emb' embed_order unembed_order uu____3597 
>>>>>>> snap
=======
  mk_emb' embed_order unembed_order uu____3663 
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
           FStar_Syntax_Syntax.ltyp = uu____3616;
           FStar_Syntax_Syntax.rng = uu____3617;_},uu____3618)
        ->
        let uu____3637 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____3637
    | uu____3638 ->
        ((let uu____3640 =
            let uu____3646 =
              let uu____3648 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3648  in
            (FStar_Errors.Warning_NotEmbedded, uu____3646)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3640);
=======
           FStar_Syntax_Syntax.ltyp = uu____3628;
           FStar_Syntax_Syntax.rng = uu____3629;_},uu____3630)
        ->
        let uu____3649 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____3649
    | uu____3650 ->
        ((let uu____3652 =
            let uu____3658 =
              let uu____3660 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3660  in
            (FStar_Errors.Warning_NotEmbedded, uu____3658)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3652);
>>>>>>> snap
=======
           FStar_Syntax_Syntax.ltyp = uu____3694;
           FStar_Syntax_Syntax.rng = uu____3695;_},uu____3696)
        ->
        let uu____3715 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____3715
    | uu____3716 ->
        ((let uu____3718 =
            let uu____3724 =
              let uu____3726 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3726  in
            (FStar_Errors.Warning_NotEmbedded, uu____3724)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3718);
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____3677 =
      let uu____3683 = FStar_Ident.range_of_id i  in
      let uu____3684 = FStar_Ident.text_of_id i  in (uu____3683, uu____3684)
       in
    FStar_TypeChecker_NBETerm.embed repr cb uu____3677  in
  let unembed_ident cb t =
    let uu____3707 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____3707 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____3731 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____3731
=======
    let uu____3689 =
      let uu____3695 = FStar_Ident.range_of_id i  in
      let uu____3696 = FStar_Ident.text_of_id i  in (uu____3695, uu____3696)
=======
    let uu____3755 =
      let uu____3761 = FStar_Ident.range_of_id i  in
      let uu____3762 = FStar_Ident.text_of_id i  in (uu____3761, uu____3762)
>>>>>>> snap
       in
    FStar_TypeChecker_NBETerm.embed repr cb uu____3755  in
  let unembed_ident cb t =
    let uu____3785 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____3785 with
    | FStar_Pervasives_Native.Some (rng,s) ->
<<<<<<< HEAD
        let uu____3743 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____3743
>>>>>>> snap
=======
        let uu____3809 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____3809
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____3741 =
      let uu____3749 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____3751 =
        let uu____3754 = fv_as_emb_typ range_fv  in
        let uu____3755 =
          let uu____3758 = fv_as_emb_typ string_fv  in [uu____3758]  in
        uu____3754 :: uu____3755  in
      (uu____3749, uu____3751)  in
    FStar_Syntax_Syntax.ET_app uu____3741  in
  let uu____3762 =
    let uu____3763 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____3764 =
      let uu____3771 =
        let uu____3776 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____3776  in
      let uu____3781 =
        let uu____3788 =
          let uu____3793 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____3793  in
        [uu____3788]  in
      uu____3771 :: uu____3781  in
    mkFV uu____3763 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____3764
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3762 et 
=======
    let uu____3753 =
      let uu____3761 =
=======
    let uu____3819 =
      let uu____3827 =
>>>>>>> snap
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____3829 =
        let uu____3832 = fv_as_emb_typ range_fv  in
        let uu____3833 =
          let uu____3836 = fv_as_emb_typ string_fv  in [uu____3836]  in
        uu____3832 :: uu____3833  in
      (uu____3827, uu____3829)  in
    FStar_Syntax_Syntax.ET_app uu____3819  in
  let uu____3840 =
    let uu____3841 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____3842 =
      let uu____3849 =
        let uu____3854 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____3854  in
      let uu____3859 =
        let uu____3866 =
          let uu____3871 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____3871  in
        [uu____3866]  in
      uu____3849 :: uu____3859  in
    mkFV uu____3841 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____3842
     in
<<<<<<< HEAD
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3774 et 
>>>>>>> snap
=======
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3840 et 
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____3850 =
          let uu____3857 =
            let uu____3862 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3862  in
          let uu____3864 =
            let uu____3871 =
              let uu____3876 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3876  in
            let uu____3877 =
              let uu____3884 =
                let uu____3889 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____3889  in
              let uu____3892 =
                let uu____3899 =
                  let uu____3904 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____3904  in
                let uu____3905 =
                  let uu____3912 =
                    let uu____3917 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____3917  in
                  [uu____3912]  in
                uu____3899 :: uu____3905  in
              uu____3884 :: uu____3892  in
            uu____3871 :: uu____3877  in
          uu____3857 :: uu____3864  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____3850
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3944 =
          let uu____3951 =
            let uu____3956 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____3956  in
          let uu____3960 =
            let uu____3967 =
              let uu____3972 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3972  in
            [uu____3967]  in
          uu____3951 :: uu____3960  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____3944
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____4002 =
          let uu____4009 =
            let uu____4014 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4014  in
          let uu____4018 =
            let uu____4025 =
              let uu____4030 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____4030  in
            let uu____4033 =
              let uu____4040 =
                let uu____4045 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____4045  in
              let uu____4046 =
                let uu____4053 =
                  let uu____4058 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4058  in
                let uu____4059 =
                  let uu____4066 =
                    let uu____4071 =
                      let uu____4072 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____4072 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4071  in
                  [uu____4066]  in
                uu____4053 :: uu____4059  in
              uu____4040 :: uu____4046  in
            uu____4025 :: uu____4033  in
          uu____4009 :: uu____4018  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____4002
=======
        let uu____3862 =
          let uu____3869 =
            let uu____3874 =
=======
        let uu____3928 =
          let uu____3935 =
            let uu____3940 =
>>>>>>> snap
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3940  in
          let uu____3942 =
            let uu____3949 =
              let uu____3954 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3954  in
            let uu____3955 =
              let uu____3962 =
                let uu____3967 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____3967  in
              let uu____3970 =
                let uu____3977 =
                  let uu____3982 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____3982  in
                let uu____3983 =
                  let uu____3990 =
                    let uu____3995 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____3995  in
                  [uu____3990]  in
                uu____3977 :: uu____3983  in
              uu____3962 :: uu____3970  in
            uu____3949 :: uu____3955  in
          uu____3935 :: uu____3942  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____3928
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4022 =
          let uu____4029 =
            let uu____4034 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4034  in
          let uu____4038 =
            let uu____4045 =
              let uu____4050 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____4050  in
            [uu____4045]  in
          uu____4029 :: uu____4038  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____4022
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____4080 =
          let uu____4087 =
            let uu____4092 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4092  in
          let uu____4096 =
            let uu____4103 =
              let uu____4108 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____4108  in
            let uu____4111 =
              let uu____4118 =
                let uu____4123 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____4123  in
              let uu____4124 =
                let uu____4131 =
                  let uu____4136 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4136  in
                let uu____4137 =
                  let uu____4144 =
                    let uu____4149 =
                      let uu____4150 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____4150 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4149  in
                  [uu____4144]  in
                uu____4131 :: uu____4137  in
              uu____4118 :: uu____4124  in
            uu____4103 :: uu____4111  in
          uu____4087 :: uu____4096  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
<<<<<<< HEAD
          uu____4014
>>>>>>> snap
=======
          uu____4080
>>>>>>> snap
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
<<<<<<< HEAD
        (fv,uu____4132,(dcs,uu____4134)::(t1,uu____4136)::(bs,uu____4138)::
         (us,uu____4140)::(nm,uu____4142)::[])
=======
        (fv,uu____4144,(dcs,uu____4146)::(t1,uu____4148)::(bs,uu____4150)::
         (us,uu____4152)::(nm,uu____4154)::[])
>>>>>>> snap
=======
        (fv,uu____4210,(dcs,uu____4212)::(t1,uu____4214)::(bs,uu____4216)::
         (us,uu____4218)::(nm,uu____4220)::[])
>>>>>>> snap
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____4177 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____4177
          (fun nm1  ->
             let uu____4195 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____4195
               (fun us1  ->
                  let uu____4209 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____4209
                    (fun bs1  ->
                       let uu____4215 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____4215
                         (fun t2  ->
                            let uu____4221 =
                              let uu____4229 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____4229 cb
                                dcs
                               in
                            FStar_Util.bind_opt uu____4221
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _4259  ->
                                      FStar_Pervasives_Native.Some _4259)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4267,(t1,uu____4269)::(ty,uu____4271)::(univs1,uu____4273)::
         (fvar1,uu____4275)::(r,uu____4277)::[])
=======
        let uu____4189 =
=======
        let uu____4255 =
>>>>>>> snap
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____4255
          (fun nm1  ->
             let uu____4273 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____4273
               (fun us1  ->
                  let uu____4287 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____4287
                    (fun bs1  ->
                       let uu____4293 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____4293
                         (fun t2  ->
                            let uu____4299 =
                              let uu____4307 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____4307 cb
                                dcs
                               in
                            FStar_Util.bind_opt uu____4299
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _4337  ->
                                      FStar_Pervasives_Native.Some _4337)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
        (fv,uu____4279,(t1,uu____4281)::(ty,uu____4283)::(univs1,uu____4285)::
         (fvar1,uu____4287)::(r,uu____4289)::[])
>>>>>>> snap
=======
        (fv,uu____4345,(t1,uu____4347)::(ty,uu____4349)::(univs1,uu____4351)::
         (fvar1,uu____4353)::(r,uu____4355)::[])
>>>>>>> snap
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____4312 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____4312
          (fun r1  ->
             let uu____4322 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1
                in
             FStar_Util.bind_opt uu____4322
               (fun fvar2  ->
                  let uu____4328 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____4328
                    (fun univs2  ->
                       let uu____4342 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____4342
                         (fun ty1  ->
                            let uu____4348 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____4348
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _4355  ->
                                      FStar_Pervasives_Native.Some _4355)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4360,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4375 ->
        ((let uu____4377 =
            let uu____4383 =
              let uu____4385 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4385
               in
            (FStar_Errors.Warning_NotEmbedded, uu____4383)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4377);
=======
        let uu____4324 =
=======
        let uu____4390 =
>>>>>>> snap
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____4390
          (fun r1  ->
             let uu____4400 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1
                in
             FStar_Util.bind_opt uu____4400
               (fun fvar2  ->
                  let uu____4406 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____4406
                    (fun univs2  ->
                       let uu____4420 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____4420
                         (fun ty1  ->
                            let uu____4426 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____4426
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _4433  ->
                                      FStar_Pervasives_Native.Some _4433)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4438,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4453 ->
        ((let uu____4455 =
            let uu____4461 =
              let uu____4463 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4463
               in
<<<<<<< HEAD
            (FStar_Errors.Warning_NotEmbedded, uu____4395)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4389);
>>>>>>> snap
=======
            (FStar_Errors.Warning_NotEmbedded, uu____4461)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4455);
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____4408 =
          let uu____4415 =
=======
        let uu____4420 =
          let uu____4427 =
>>>>>>> snap
=======
        let uu____4486 =
          let uu____4493 =
>>>>>>> snap
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
<<<<<<< HEAD
<<<<<<< HEAD
          [uu____4415]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4408
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____4430 =
          let uu____4437 =
            let uu____4442 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4442  in
          let uu____4443 =
            let uu____4450 =
              let uu____4455 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4455  in
            [uu____4450]  in
          uu____4437 :: uu____4443  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4430
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4484,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4500,(i,uu____4502)::[])
=======
          [uu____4427]  in
=======
          [uu____4493]  in
>>>>>>> snap
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4486
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____4508 =
          let uu____4515 =
            let uu____4520 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4520  in
          let uu____4521 =
            let uu____4528 =
              let uu____4533 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4533  in
            [uu____4528]  in
          uu____4515 :: uu____4521  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4508
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4562,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
<<<<<<< HEAD
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4512,(i,uu____4514)::[])
>>>>>>> snap
=======
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4578,(i,uu____4580)::[])
>>>>>>> snap
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____4521 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____4521
          (fun i1  ->
             FStar_All.pipe_left
               (fun _4528  -> FStar_Pervasives_Native.Some _4528)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4530,(e2,uu____4532)::(e1,uu____4534)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____4557 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____4557
          (fun e11  ->
             let uu____4563 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____4563
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _4570  -> FStar_Pervasives_Native.Some _4570)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____4571 ->
        ((let uu____4573 =
            let uu____4579 =
              let uu____4581 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4581  in
            (FStar_Errors.Warning_NotEmbedded, uu____4579)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4573);
=======
        let uu____4533 =
=======
        let uu____4599 =
>>>>>>> snap
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____4599
          (fun i1  ->
             FStar_All.pipe_left
               (fun _4606  -> FStar_Pervasives_Native.Some _4606)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4608,(e2,uu____4610)::(e1,uu____4612)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____4635 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____4635
          (fun e11  ->
             let uu____4641 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____4641
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _4648  -> FStar_Pervasives_Native.Some _4648)
                    (FStar_Reflection_Data.Mult (e11, e21))))
<<<<<<< HEAD
    | uu____4583 ->
        ((let uu____4585 =
            let uu____4591 =
              let uu____4593 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4593  in
            (FStar_Errors.Warning_NotEmbedded, uu____4591)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4585);
>>>>>>> snap
=======
    | uu____4649 ->
        ((let uu____4651 =
            let uu____4657 =
              let uu____4659 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4659  in
            (FStar_Errors.Warning_NotEmbedded, uu____4657)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4651);
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____4610 = FStar_Ident.path_of_lid lid  in
    FStar_TypeChecker_NBETerm.embed e_string_list rng uu____4610  in
  let unembed1 cb t =
    let uu____4632 = FStar_TypeChecker_NBETerm.unembed e_string_list cb t  in
    FStar_Util.map_opt uu____4632
      (fun p  -> FStar_Ident.lid_of_path p FStar_Range.dummyRange)
     in
  let uu____4649 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____4654 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed1 unembed1 uu____4649 uu____4654 
=======
    let uu____4622 = FStar_Ident.path_of_lid lid  in
    FStar_TypeChecker_NBETerm.embed e_string_list rng uu____4622  in
=======
    let uu____4688 = FStar_Ident.path_of_lid lid  in
    FStar_TypeChecker_NBETerm.embed e_string_list rng uu____4688  in
>>>>>>> snap
  let unembed1 cb t =
    let uu____4710 = FStar_TypeChecker_NBETerm.unembed e_string_list cb t  in
    FStar_Util.map_opt uu____4710
      (fun p  -> FStar_Ident.lid_of_path p FStar_Range.dummyRange)
     in
  let uu____4727 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____4732 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
<<<<<<< HEAD
  FStar_TypeChecker_NBETerm.mk_emb embed1 unembed1 uu____4661 uu____4666 
>>>>>>> snap
=======
  FStar_TypeChecker_NBETerm.mk_emb embed1 unembed1 uu____4727 uu____4732 
>>>>>>> snap
let (e_qualifier :
  FStar_Syntax_Syntax.qualifier FStar_TypeChecker_NBETerm.embedding) =
  let embed1 cb q =
    match q with
    | FStar_Syntax_Syntax.Assumption  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.New  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.fv [] []
    | FStar_Syntax_Syntax.Private  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.fv []
          []
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.Visible_default  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.Irreducible  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.Abstract  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Abstract.FStar_Reflection_Data.fv []
          []
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.NoExtract  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.Noeq  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.fv [] []
    | FStar_Syntax_Syntax.Unopteq  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.fv []
          []
    | FStar_Syntax_Syntax.TotalEffect  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.Logic  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.fv [] []
    | FStar_Syntax_Syntax.Reifiable  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.HasMaskedEffect  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.fv
          [] []
    | FStar_Syntax_Syntax.Effect  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.fv []
          []
    | FStar_Syntax_Syntax.OnlyName  ->
        mkConstruct
          FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.fv []
          []
    | FStar_Syntax_Syntax.Reflectable l ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____4742 =
          let uu____4749 =
            let uu____4754 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____4754  in
          [uu____4749]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.fv
          [] uu____4742
    | FStar_Syntax_Syntax.Discriminator l ->
        let uu____4764 =
          let uu____4771 =
            let uu____4776 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____4776  in
          [uu____4771]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.fv
          [] uu____4764
    | FStar_Syntax_Syntax.Action l ->
        let uu____4786 =
          let uu____4793 =
            let uu____4798 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____4798  in
          [uu____4793]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.fv []
          uu____4786
    | FStar_Syntax_Syntax.Projector (l,i) ->
        let uu____4809 =
          let uu____4816 =
            let uu____4821 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____4821  in
          let uu____4822 =
            let uu____4829 =
              let uu____4834 = FStar_TypeChecker_NBETerm.embed e_ident cb i
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____4834  in
            [uu____4829]  in
          uu____4816 :: uu____4822  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.fv
          [] uu____4809
    | FStar_Syntax_Syntax.RecordType (ids1,ids2) ->
        let uu____4857 =
          let uu____4864 =
            let uu____4869 =
              let uu____4870 = FStar_TypeChecker_NBETerm.e_list e_ident  in
              FStar_TypeChecker_NBETerm.embed uu____4870 cb ids1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4869  in
          let uu____4877 =
            let uu____4884 =
              let uu____4889 =
                let uu____4890 = FStar_TypeChecker_NBETerm.e_list e_ident  in
                FStar_TypeChecker_NBETerm.embed uu____4890 cb ids2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4889  in
            [uu____4884]  in
          uu____4864 :: uu____4877  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.fv
          [] uu____4857
    | FStar_Syntax_Syntax.RecordConstructor (ids1,ids2) ->
        let uu____4919 =
          let uu____4926 =
            let uu____4931 =
              let uu____4932 = FStar_TypeChecker_NBETerm.e_list e_ident  in
              FStar_TypeChecker_NBETerm.embed uu____4932 cb ids1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4931  in
          let uu____4939 =
            let uu____4946 =
              let uu____4951 =
                let uu____4952 = FStar_TypeChecker_NBETerm.e_list e_ident  in
                FStar_TypeChecker_NBETerm.embed uu____4952 cb ids2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4951  in
            [uu____4946]  in
          uu____4926 :: uu____4939  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.fv
          [] uu____4919
=======
        let uu____4754 =
          let uu____4761 =
            let uu____4766 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____4766  in
          [uu____4761]  in
=======
        let uu____4820 =
          let uu____4827 =
            let uu____4832 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____4832  in
          [uu____4827]  in
>>>>>>> snap
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.fv
          [] uu____4820
    | FStar_Syntax_Syntax.Discriminator l ->
        let uu____4842 =
          let uu____4849 =
            let uu____4854 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____4854  in
          [uu____4849]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.fv
          [] uu____4842
    | FStar_Syntax_Syntax.Action l ->
        let uu____4864 =
          let uu____4871 =
            let uu____4876 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____4876  in
          [uu____4871]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.fv []
          uu____4864
    | FStar_Syntax_Syntax.Projector (l,i) ->
        let uu____4887 =
          let uu____4894 =
            let uu____4899 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____4899  in
          let uu____4900 =
            let uu____4907 =
              let uu____4912 = FStar_TypeChecker_NBETerm.embed e_ident cb i
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____4912  in
            [uu____4907]  in
          uu____4894 :: uu____4900  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.fv
          [] uu____4887
    | FStar_Syntax_Syntax.RecordType (ids1,ids2) ->
        let uu____4935 =
          let uu____4942 =
            let uu____4947 =
              let uu____4948 = FStar_TypeChecker_NBETerm.e_list e_ident  in
              FStar_TypeChecker_NBETerm.embed uu____4948 cb ids1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4947  in
          let uu____4955 =
            let uu____4962 =
              let uu____4967 =
                let uu____4968 = FStar_TypeChecker_NBETerm.e_list e_ident  in
                FStar_TypeChecker_NBETerm.embed uu____4968 cb ids2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4967  in
            [uu____4962]  in
          uu____4942 :: uu____4955  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.fv
          [] uu____4935
    | FStar_Syntax_Syntax.RecordConstructor (ids1,ids2) ->
        let uu____4997 =
          let uu____5004 =
            let uu____5009 =
              let uu____5010 = FStar_TypeChecker_NBETerm.e_list e_ident  in
              FStar_TypeChecker_NBETerm.embed uu____5010 cb ids1  in
            FStar_TypeChecker_NBETerm.as_arg uu____5009  in
          let uu____5017 =
            let uu____5024 =
              let uu____5029 =
                let uu____5030 = FStar_TypeChecker_NBETerm.e_list e_ident  in
                FStar_TypeChecker_NBETerm.embed uu____5030 cb ids2  in
              FStar_TypeChecker_NBETerm.as_arg uu____5029  in
            [uu____5024]  in
          uu____5004 :: uu____5017  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.fv
<<<<<<< HEAD
          [] uu____4931
>>>>>>> snap
=======
          [] uu____4997
>>>>>>> snap
     in
  let unembed1 cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Assumption
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.New
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Private
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.lid
        ->
        FStar_Pervasives_Native.Some
          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Visible_default
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Irreducible
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Abstract.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Abstract
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.lid
        ->
        FStar_Pervasives_Native.Some
          FStar_Syntax_Syntax.Inline_for_extraction
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.NoExtract
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Noeq
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Unopteq
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.TotalEffect
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Logic
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Reifiable
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.lid
        ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.ExceptionConstructor
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.HasMaskedEffect
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Effect
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.OnlyName
<<<<<<< HEAD
<<<<<<< HEAD
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5222)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
        ->
        let uu____5239 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5239
          (fun l1  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Reflectable l1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5246)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
        ->
        let uu____5263 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5263
          (fun l1  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Discriminator l1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5270)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
        ->
        let uu____5287 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5287
          (fun l1  ->
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Action l1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,[],(i,uu____5294)::(l,uu____5296)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
        ->
        let uu____5317 = FStar_TypeChecker_NBETerm.unembed e_ident cb i  in
        FStar_Util.bind_opt uu____5317
          (fun i1  ->
             let uu____5323 = FStar_TypeChecker_NBETerm.unembed e_lid cb l
                in
             FStar_Util.bind_opt uu____5323
=======
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5234)::[]) when
=======
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5300)::[]) when
>>>>>>> snap
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
        ->
        let uu____5317 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5317
          (fun l1  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Reflectable l1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5324)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
        ->
        let uu____5341 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5341
          (fun l1  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Discriminator l1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5348)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
        ->
        let uu____5365 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5365
          (fun l1  ->
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Action l1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,[],(i,uu____5372)::(l,uu____5374)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
        ->
        let uu____5395 = FStar_TypeChecker_NBETerm.unembed e_ident cb i  in
        FStar_Util.bind_opt uu____5395
          (fun i1  ->
             let uu____5401 = FStar_TypeChecker_NBETerm.unembed e_lid cb l
                in
<<<<<<< HEAD
             FStar_Util.bind_opt uu____5335
>>>>>>> snap
=======
             FStar_Util.bind_opt uu____5401
>>>>>>> snap
               (fun l1  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Projector (l1, i1))))
    | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
<<<<<<< HEAD
        (fv,[],(ids2,uu____5330)::(ids1,uu____5332)::[]) when
=======
        (fv,[],(ids2,uu____5342)::(ids1,uu____5344)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
        ->
        let uu____5365 =
          let uu____5370 = FStar_TypeChecker_NBETerm.e_list e_ident  in
          FStar_TypeChecker_NBETerm.unembed uu____5370 cb ids1  in
        FStar_Util.bind_opt uu____5365
          (fun ids11  ->
             let uu____5384 =
               let uu____5389 = FStar_TypeChecker_NBETerm.e_list e_ident  in
               FStar_TypeChecker_NBETerm.unembed uu____5389 cb ids2  in
             FStar_Util.bind_opt uu____5384
               (fun ids21  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.RecordType (ids11, ids21))))
    | FStar_TypeChecker_NBETerm.Construct
=======
>>>>>>> snap
        (fv,[],(ids2,uu____5408)::(ids1,uu____5410)::[]) when
>>>>>>> snap
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
        ->
        let uu____5431 =
          let uu____5436 = FStar_TypeChecker_NBETerm.e_list e_ident  in
          FStar_TypeChecker_NBETerm.unembed uu____5436 cb ids1  in
        FStar_Util.bind_opt uu____5431
          (fun ids11  ->
             let uu____5450 =
               let uu____5455 = FStar_TypeChecker_NBETerm.e_list e_ident  in
               FStar_TypeChecker_NBETerm.unembed uu____5455 cb ids2  in
             FStar_Util.bind_opt uu____5450
               (fun ids21  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.RecordType (ids11, ids21))))
    | FStar_TypeChecker_NBETerm.Construct
<<<<<<< HEAD
        (fv,[],(ids2,uu____5396)::(ids1,uu____5398)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
        ->
        let uu____5419 =
          let uu____5424 = FStar_TypeChecker_NBETerm.e_list e_ident  in
          FStar_TypeChecker_NBETerm.unembed uu____5424 cb ids1  in
        FStar_Util.bind_opt uu____5419
          (fun ids11  ->
             let uu____5438 =
               let uu____5443 = FStar_TypeChecker_NBETerm.e_list e_ident  in
               FStar_TypeChecker_NBETerm.unembed uu____5443 cb ids2  in
             FStar_Util.bind_opt uu____5438
               (fun ids21  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.RecordConstructor (ids11, ids21))))
<<<<<<< HEAD
    | uu____5460 ->
        ((let uu____5462 =
            let uu____5468 =
              let uu____5470 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded qualifier: %s" uu____5470
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5468)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5462);
         FStar_Pervasives_Native.None)
     in
  let uu____5474 =
    mkConstruct FStar_Reflection_Data.fstar_refl_qualifier_fv [] []  in
  let uu____5479 =
    fv_as_emb_typ FStar_Reflection_Data.fstar_refl_qualifier_fv  in
  FStar_TypeChecker_NBETerm.mk_emb embed1 unembed1 uu____5474 uu____5479 
=======
    | uu____5472 ->
        ((let uu____5474 =
            let uu____5480 =
              let uu____5482 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded qualifier: %s" uu____5482
=======
        (fv,[],(ids2,uu____5474)::(ids1,uu____5476)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
        ->
        let uu____5497 =
          let uu____5502 = FStar_TypeChecker_NBETerm.e_list e_ident  in
          FStar_TypeChecker_NBETerm.unembed uu____5502 cb ids1  in
        FStar_Util.bind_opt uu____5497
          (fun ids11  ->
             let uu____5516 =
               let uu____5521 = FStar_TypeChecker_NBETerm.e_list e_ident  in
               FStar_TypeChecker_NBETerm.unembed uu____5521 cb ids2  in
             FStar_Util.bind_opt uu____5516
               (fun ids21  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.RecordConstructor (ids11, ids21))))
    | uu____5538 ->
        ((let uu____5540 =
            let uu____5546 =
              let uu____5548 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded qualifier: %s" uu____5548
>>>>>>> snap
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5546)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5540);
         FStar_Pervasives_Native.None)
     in
  let uu____5552 =
    mkConstruct FStar_Reflection_Data.fstar_refl_qualifier_fv [] []  in
  let uu____5557 =
    fv_as_emb_typ FStar_Reflection_Data.fstar_refl_qualifier_fv  in
<<<<<<< HEAD
  FStar_TypeChecker_NBETerm.mk_emb embed1 unembed1 uu____5486 uu____5491 
>>>>>>> snap
=======
  FStar_TypeChecker_NBETerm.mk_emb embed1 unembed1 uu____5552 uu____5557 
>>>>>>> snap
let (e_qualifiers :
  FStar_Syntax_Syntax.qualifier Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_qualifier 