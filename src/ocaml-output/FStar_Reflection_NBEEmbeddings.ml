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
  'uuuuuu99 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'uuuuuu99 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'uuuuuu99 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'uuuuuu99 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____141 = mkFV fv [] []  in
        let uu____146 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____141 uu____146
  
let mk_lazy :
  'uuuuuu158 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'uuuuuu158 ->
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
          let thunk =
            FStar_Thunk.mk
              (fun uu____190  ->
                 let uu____191 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____191)
             in
          FStar_TypeChecker_NBETerm.mk_t
            (FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk))
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv cb bv =
    mk_lazy cb bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv
     in
  let unembed_bv cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
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
    match t.FStar_TypeChecker_NBETerm.nbe_t with
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
    match t.FStar_TypeChecker_NBETerm.nbe_t with
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
      FStar_TypeChecker_NBETerm.mk_t
        (FStar_TypeChecker_NBETerm.Quote (t, qi))
       in
    let rec unembed_term cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
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
    match t.FStar_TypeChecker_NBETerm.nbe_t with
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
    match t.FStar_TypeChecker_NBETerm.nbe_t with
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
    match t.FStar_TypeChecker_NBETerm.nbe_t with
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
    match t.FStar_TypeChecker_NBETerm.nbe_t with
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
            let uu____916 =
              FStar_All.pipe_left FStar_TypeChecker_NBETerm.mk_t
                (FStar_TypeChecker_NBETerm.Constant
                   (FStar_TypeChecker_NBETerm.Int i))
               in
            FStar_TypeChecker_NBETerm.as_arg uu____916  in
          [uu____911]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____904
    | FStar_Reflection_Data.C_String s ->
        let uu____927 =
          let uu____934 =
            let uu____939 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____939  in
          [uu____934]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____927
    | FStar_Reflection_Data.C_Range r ->
        let uu____950 =
          let uu____957 =
            let uu____962 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____962  in
          [uu____957]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____950
    | FStar_Reflection_Data.C_Reify  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____976 =
          let uu____983 =
            let uu____988 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string_list cb ns
               in
            FStar_TypeChecker_NBETerm.as_arg uu____988  in
          [uu____983]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv []
          uu____976
     in
  let unembed_const cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____1056)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____1073 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____1073
          (fun i1  ->
             FStar_All.pipe_left
               (fun uu____1080  -> FStar_Pervasives_Native.Some uu____1080)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____1083)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____1100 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1100
          (fun s1  ->
             FStar_All.pipe_left
               (fun uu____1111  -> FStar_Pervasives_Native.Some uu____1111)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____1114)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____1131 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____1131
          (fun r1  ->
             FStar_All.pipe_left
               (fun uu____1138  -> FStar_Pervasives_Native.Some uu____1138)
               (FStar_Reflection_Data.C_Range r1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Reify
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(ns,uu____1154)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
        ->
        let uu____1171 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string_list cb ns
           in
        FStar_Util.bind_opt uu____1171
          (fun ns1  ->
             FStar_All.pipe_left
               (fun uu____1190  -> FStar_Pervasives_Native.Some uu____1190)
               (FStar_Reflection_Data.C_Reflect ns1))
    | uu____1191 ->
        ((let uu____1193 =
            let uu____1199 =
              let uu____1201 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____1201  in
            (FStar_Errors.Warning_NotEmbedded, uu____1199)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1193);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____1212  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1225 =
            let uu____1232 =
              let uu____1237 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1237  in
            [uu____1232]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____1225
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1262 =
            let uu____1269 =
              let uu____1274 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1274  in
            let uu____1275 =
              let uu____1282 =
                let uu____1287 =
                  let uu____1288 =
                    let uu____1298 =
                      let uu____1306 = e_pattern' ()  in
                      FStar_TypeChecker_NBETerm.e_tuple2 uu____1306
                        FStar_TypeChecker_NBETerm.e_bool
                       in
                    FStar_TypeChecker_NBETerm.e_list uu____1298  in
                  FStar_TypeChecker_NBETerm.embed uu____1288 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____1287  in
              [uu____1282]  in
            uu____1269 :: uu____1275  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1262
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1335 =
            let uu____1342 =
              let uu____1347 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1347  in
            [uu____1342]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1335
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1357 =
            let uu____1364 =
              let uu____1369 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1369  in
            [uu____1364]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1357
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1380 =
            let uu____1387 =
              let uu____1392 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1392  in
            let uu____1393 =
              let uu____1400 =
                let uu____1405 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1405  in
              [uu____1400]  in
            uu____1387 :: uu____1393  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1380
       in
    let unembed_pattern cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____1435)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1452 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____1452
            (fun c1  ->
               FStar_All.pipe_left
                 (fun uu____1459  -> FStar_Pervasives_Native.Some uu____1459)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____1462)::(f,uu____1464)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1485 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____1485
            (fun f1  ->
               let uu____1491 =
                 let uu____1501 =
                   let uu____1511 =
                     let uu____1519 = e_pattern' ()  in
                     FStar_TypeChecker_NBETerm.e_tuple2 uu____1519
                       FStar_TypeChecker_NBETerm.e_bool
                      in
                   FStar_TypeChecker_NBETerm.e_list uu____1511  in
                 FStar_TypeChecker_NBETerm.unembed uu____1501 cb ps  in
               FStar_Util.bind_opt uu____1491
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun uu____1553  ->
                         FStar_Pervasives_Native.Some uu____1553)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1563)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1580 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1580
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun uu____1587  -> FStar_Pervasives_Native.Some uu____1587)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1590)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1607 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1607
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun uu____1614  -> FStar_Pervasives_Native.Some uu____1614)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____1617)::(bv,uu____1619)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1640 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1640
            (fun bv1  ->
               let uu____1646 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____1646
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun uu____1653  ->
                         FStar_Pervasives_Native.Some uu____1653)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1654 ->
          ((let uu____1656 =
              let uu____1662 =
                let uu____1664 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1664
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1662)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1656);
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
    let uu____1705 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1705
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1736 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1736 e_aqualv
  
let unlazy_as_t :
  'uuuuuu1746 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'uuuuuu1746
  =
  fun k  ->
    fun t  ->
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____1759;
             FStar_Syntax_Syntax.rng = uu____1760;_},uu____1761)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____1780 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1818 =
            let uu____1825 =
              let uu____1830 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1830  in
            [uu____1825]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1818
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1840 =
            let uu____1847 =
              let uu____1852 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1852  in
            [uu____1847]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1840
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1862 =
            let uu____1869 =
              let uu____1874 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1874  in
            [uu____1869]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1862
      | FStar_Reflection_Data.Tv_App (hd,a) ->
          let uu____1885 =
            let uu____1892 =
              let uu____1897 =
                let uu____1898 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1898 cb hd  in
              FStar_TypeChecker_NBETerm.as_arg uu____1897  in
            let uu____1901 =
              let uu____1908 =
                let uu____1913 =
                  let uu____1914 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1914 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1913  in
              [uu____1908]  in
            uu____1892 :: uu____1901  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1885
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1939 =
            let uu____1946 =
              let uu____1951 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1951  in
            let uu____1952 =
              let uu____1959 =
                let uu____1964 =
                  let uu____1965 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1965 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1964  in
              [uu____1959]  in
            uu____1946 :: uu____1952  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1939
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1982 =
            let uu____1989 =
              let uu____1994 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1994  in
            let uu____1995 =
              let uu____2002 =
                let uu____2007 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2007  in
              [uu____2002]  in
            uu____1989 :: uu____1995  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1982
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2021 =
            let uu____2028 =
              let uu____2033 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2033  in
            [uu____2028]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____2021
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____2044 =
            let uu____2051 =
              let uu____2056 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____2056  in
            let uu____2057 =
              let uu____2064 =
                let uu____2069 =
                  let uu____2070 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2070 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2069  in
              [uu____2064]  in
            uu____2051 :: uu____2057  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____2044
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2086 =
            let uu____2093 =
              let uu____2098 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2098  in
            [uu____2093]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____2086
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2109 =
            let uu____2116 =
              let uu____2121 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2121  in
            let uu____2122 =
              let uu____2129 =
                let uu____2134 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2134  in
              [uu____2129]  in
            uu____2116 :: uu____2122  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____2109
      | FStar_Reflection_Data.Tv_Let (r,attrs,b,t1,t2) ->
          let uu____2162 =
            let uu____2169 =
              let uu____2174 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2174  in
            let uu____2176 =
              let uu____2183 =
                let uu____2188 =
                  let uu____2189 = FStar_TypeChecker_NBETerm.e_list e_term
                     in
                  FStar_TypeChecker_NBETerm.embed uu____2189 cb attrs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2188  in
              let uu____2196 =
                let uu____2203 =
                  let uu____2208 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____2208  in
                let uu____2209 =
                  let uu____2216 =
                    let uu____2221 =
                      let uu____2222 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____2222 cb t1  in
                    FStar_TypeChecker_NBETerm.as_arg uu____2221  in
                  let uu____2225 =
                    let uu____2232 =
                      let uu____2237 =
                        let uu____2238 = e_term_aq aq  in
                        FStar_TypeChecker_NBETerm.embed uu____2238 cb t2  in
                      FStar_TypeChecker_NBETerm.as_arg uu____2237  in
                    [uu____2232]  in
                  uu____2216 :: uu____2225  in
                uu____2203 :: uu____2209  in
              uu____2183 :: uu____2196  in
            uu____2169 :: uu____2176  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____2162
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____2271 =
            let uu____2278 =
              let uu____2283 =
                let uu____2284 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2284 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____2283  in
            let uu____2287 =
              let uu____2294 =
                let uu____2299 =
                  let uu____2300 =
                    let uu____2309 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____2309  in
                  FStar_TypeChecker_NBETerm.embed uu____2300 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2299  in
              [uu____2294]  in
            uu____2278 :: uu____2287  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2271
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____2345 =
            let uu____2352 =
              let uu____2357 =
                let uu____2358 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2358 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2357  in
            let uu____2361 =
              let uu____2368 =
                let uu____2373 =
                  let uu____2374 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2374 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2373  in
              let uu____2377 =
                let uu____2384 =
                  let uu____2389 =
                    let uu____2390 =
                      let uu____2395 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2395  in
                    FStar_TypeChecker_NBETerm.embed uu____2390 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2389  in
                [uu____2384]  in
              uu____2368 :: uu____2377  in
            uu____2352 :: uu____2361  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2345
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2423 =
            let uu____2430 =
              let uu____2435 =
                let uu____2436 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2436 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2435  in
            let uu____2439 =
              let uu____2446 =
                let uu____2451 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2451  in
              let uu____2452 =
                let uu____2459 =
                  let uu____2464 =
                    let uu____2465 =
                      let uu____2470 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2470  in
                    FStar_TypeChecker_NBETerm.embed uu____2465 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2464  in
                [uu____2459]  in
              uu____2446 :: uu____2452  in
            uu____2430 :: uu____2439  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2423
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t.FStar_TypeChecker_NBETerm.nbe_t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2511,(b,uu____2513)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2532 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2532
            (fun b1  ->
               FStar_All.pipe_left
                 (fun uu____2539  -> FStar_Pervasives_Native.Some uu____2539)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2541,(b,uu____2543)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2562 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2562
            (fun b1  ->
               FStar_All.pipe_left
                 (fun uu____2569  -> FStar_Pervasives_Native.Some uu____2569)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2571,(f,uu____2573)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2592 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____2592
            (fun f1  ->
               FStar_All.pipe_left
                 (fun uu____2599  -> FStar_Pervasives_Native.Some uu____2599)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2601,(r,uu____2603)::(l,uu____2605)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2628 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____2628
            (fun l1  ->
               let uu____2634 = FStar_TypeChecker_NBETerm.unembed e_argv cb r
                  in
               FStar_Util.bind_opt uu____2634
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun uu____2641  ->
                         FStar_Pervasives_Native.Some uu____2641)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2643,(t1,uu____2645)::(b,uu____2647)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2670 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2670
            (fun b1  ->
               let uu____2676 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2676
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun uu____2683  ->
                         FStar_Pervasives_Native.Some uu____2683)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2685,(t1,uu____2687)::(b,uu____2689)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2712 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2712
            (fun b1  ->
               let uu____2718 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____2718
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun uu____2725  ->
                         FStar_Pervasives_Native.Some uu____2725)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2727,(u,uu____2729)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2748 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____2748
            (fun u1  ->
               FStar_All.pipe_left
                 (fun uu____2755  -> FStar_Pervasives_Native.Some uu____2755)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2757,(t1,uu____2759)::(b,uu____2761)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2784 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2784
            (fun b1  ->
               let uu____2790 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2790
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun uu____2797  ->
                         FStar_Pervasives_Native.Some uu____2797)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2799,(c,uu____2801)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2820 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____2820
            (fun c1  ->
               FStar_All.pipe_left
                 (fun uu____2827  -> FStar_Pervasives_Native.Some uu____2827)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2829,(l,uu____2831)::(u,uu____2833)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2856 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____2856
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun uu____2865  -> FStar_Pervasives_Native.Some uu____2865)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2867,(t2,uu____2869)::(t1,uu____2871)::(b,uu____2873)::
           (attrs,uu____2875)::(r,uu____2877)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2912 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____2912
            (fun r1  ->
               let uu____2922 =
                 let uu____2927 = FStar_TypeChecker_NBETerm.e_list e_term  in
                 FStar_TypeChecker_NBETerm.unembed uu____2927 cb attrs  in
               FStar_Util.bind_opt uu____2922
                 (fun attrs1  ->
                    let uu____2941 =
                      FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
                    FStar_Util.bind_opt uu____2941
                      (fun b1  ->
                         let uu____2947 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                         FStar_Util.bind_opt uu____2947
                           (fun t11  ->
                              let uu____2953 =
                                FStar_TypeChecker_NBETerm.unembed e_term cb
                                  t2
                                 in
                              FStar_Util.bind_opt uu____2953
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun uu____2960  ->
                                        FStar_Pervasives_Native.Some
                                          uu____2960)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, attrs1, b1, t11, t21)))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2965,(brs,uu____2967)::(t1,uu____2969)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2992 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
          FStar_Util.bind_opt uu____2992
            (fun t2  ->
               let uu____2998 =
                 let uu____3003 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____3003 cb brs  in
               FStar_Util.bind_opt uu____2998
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun uu____3018  ->
                         FStar_Pervasives_Native.Some uu____3018)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____3022,(tacopt,uu____3024)::(t1,uu____3026)::(e,uu____3028)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____3055 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____3055
            (fun e1  ->
               let uu____3061 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____3061
                 (fun t2  ->
                    let uu____3067 =
                      let uu____3072 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3072 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3067
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun uu____3087  ->
                              FStar_Pervasives_Native.Some uu____3087)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____3091,(tacopt,uu____3093)::(c,uu____3095)::(e,uu____3097)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____3124 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____3124
            (fun e1  ->
               let uu____3130 = FStar_TypeChecker_NBETerm.unembed e_comp cb c
                  in
               FStar_Util.bind_opt uu____3130
                 (fun c1  ->
                    let uu____3136 =
                      let uu____3141 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3141 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3136
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun uu____3156  ->
                              FStar_Pervasives_Native.Some uu____3156)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____3160,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun uu____3177  -> FStar_Pervasives_Native.Some uu____3177)
            FStar_Reflection_Data.Tv_Unknown
      | uu____3178 ->
          ((let uu____3180 =
              let uu____3186 =
                let uu____3188 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____3188
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3186)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3180);
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
    let uu____3215 =
      let uu____3222 =
        let uu____3227 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____3227  in
      let uu____3229 =
        let uu____3236 =
          let uu____3241 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____3241  in
        let uu____3242 =
          let uu____3249 =
            let uu____3254 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3254  in
          [uu____3249]  in
        uu____3236 :: uu____3242  in
      uu____3222 :: uu____3229  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____3215
     in
  let unembed_bv_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3287,(s,uu____3289)::(idx,uu____3291)::(nm,uu____3293)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____3320 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____3320
          (fun nm1  ->
             let uu____3330 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____3330
               (fun idx1  ->
                  let uu____3336 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____3336
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun uu____3343  ->
                            FStar_Pervasives_Native.Some uu____3343)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____3344 ->
        ((let uu____3346 =
            let uu____3352 =
              let uu____3354 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3354  in
            (FStar_Errors.Warning_NotEmbedded, uu____3352)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3346);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____3378 =
          let uu____3385 =
            let uu____3390 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3390  in
          let uu____3391 =
            let uu____3398 =
              let uu____3403 =
                let uu____3404 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____3404 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3403  in
            [uu____3398]  in
          uu____3385 :: uu____3391  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3378
    | FStar_Reflection_Data.C_GTotal (t,md) ->
        let uu____3429 =
          let uu____3436 =
            let uu____3441 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3441  in
          let uu____3442 =
            let uu____3449 =
              let uu____3454 =
                let uu____3455 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____3455 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3454  in
            [uu____3449]  in
          uu____3436 :: uu____3442  in
        mkConstruct
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.fv []
          uu____3429
    | FStar_Reflection_Data.C_Lemma (pre,post,pats) ->
        let uu____3477 =
          let uu____3484 =
            let uu____3489 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3489  in
          let uu____3490 =
            let uu____3497 =
              let uu____3502 = FStar_TypeChecker_NBETerm.embed e_term cb post
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3502  in
            let uu____3503 =
              let uu____3510 =
                let uu____3515 =
                  FStar_TypeChecker_NBETerm.embed e_term cb pats  in
                FStar_TypeChecker_NBETerm.as_arg uu____3515  in
              [uu____3510]  in
            uu____3497 :: uu____3503  in
          uu____3484 :: uu____3490  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3477
    | FStar_Reflection_Data.C_Eff (us,eff,res,args) ->
        let uu____3544 =
          let uu____3551 =
            let uu____3556 =
              let uu____3557 =
                FStar_TypeChecker_NBETerm.e_list
                  FStar_TypeChecker_NBETerm.e_unit
                 in
              FStar_TypeChecker_NBETerm.embed uu____3557 cb us  in
            FStar_TypeChecker_NBETerm.as_arg uu____3556  in
          let uu____3564 =
            let uu____3571 =
              let uu____3576 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_string_list cb eff
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3576  in
            let uu____3580 =
              let uu____3587 =
                let uu____3592 =
                  FStar_TypeChecker_NBETerm.embed e_term cb res  in
                FStar_TypeChecker_NBETerm.as_arg uu____3592  in
              let uu____3593 =
                let uu____3600 =
                  let uu____3605 =
                    let uu____3606 = FStar_TypeChecker_NBETerm.e_list e_argv
                       in
                    FStar_TypeChecker_NBETerm.embed uu____3606 cb args  in
                  FStar_TypeChecker_NBETerm.as_arg uu____3605  in
                [uu____3600]  in
              uu____3587 :: uu____3593  in
            uu____3571 :: uu____3580  in
          uu____3551 :: uu____3564  in
        mkConstruct FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.fv
          [] uu____3544
     in
  let unembed_comp_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3649,(md,uu____3651)::(t1,uu____3653)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3676 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3676
          (fun t2  ->
             let uu____3682 =
               let uu____3687 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3687 cb md  in
             FStar_Util.bind_opt uu____3682
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun uu____3702  ->
                       FStar_Pervasives_Native.Some uu____3702)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3706,(md,uu____3708)::(t1,uu____3710)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
        ->
        let uu____3733 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3733
          (fun t2  ->
             let uu____3739 =
               let uu____3744 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3744 cb md  in
             FStar_Util.bind_opt uu____3739
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun uu____3759  ->
                       FStar_Pervasives_Native.Some uu____3759)
                    (FStar_Reflection_Data.C_GTotal (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3763,(post,uu____3765)::(pre,uu____3767)::(pats,uu____3769)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3796 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____3796
          (fun pre1  ->
             let uu____3802 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____3802
               (fun post1  ->
                  let uu____3808 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb pats  in
                  FStar_Util.bind_opt uu____3808
                    (fun pats1  ->
                       FStar_All.pipe_left
                         (fun uu____3815  ->
                            FStar_Pervasives_Native.Some uu____3815)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1, pats1)))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3817,(args,uu____3819)::(res,uu____3821)::(eff,uu____3823)::
         (us,uu____3825)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
        ->
        let uu____3856 =
          let uu____3861 =
            FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_unit
             in
          FStar_TypeChecker_NBETerm.unembed uu____3861 cb us  in
        FStar_Util.bind_opt uu____3856
          (fun us1  ->
             let uu____3875 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_string_list cb eff
                in
             FStar_Util.bind_opt uu____3875
               (fun eff1  ->
                  let uu____3893 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb res  in
                  FStar_Util.bind_opt uu____3893
                    (fun res1  ->
                       let uu____3899 =
                         let uu____3904 =
                           FStar_TypeChecker_NBETerm.e_list e_argv  in
                         FStar_TypeChecker_NBETerm.unembed uu____3904 cb args
                          in
                       FStar_Util.bind_opt uu____3899
                         (fun args1  ->
                            FStar_All.pipe_left
                              (fun uu____3919  ->
                                 FStar_Pervasives_Native.Some uu____3919)
                              (FStar_Reflection_Data.C_Eff
                                 (us1, eff1, res1, args1))))))
    | uu____3924 ->
        ((let uu____3926 =
            let uu____3932 =
              let uu____3934 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3934
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3932)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3926);
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
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3980,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3996,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4012,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____4027 ->
        ((let uu____4029 =
            let uu____4035 =
              let uu____4037 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____4037  in
            (FStar_Errors.Warning_NotEmbedded, uu____4035)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4029);
         FStar_Pervasives_Native.None)
     in
  let uu____4041 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____4041 
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt cb se =
    mk_lazy cb se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt
     in
  let unembed_sigelt cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Lazy
        (FStar_Util.Inl
         { FStar_Syntax_Syntax.blob = b;
           FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
           FStar_Syntax_Syntax.ltyp = uu____4072;
           FStar_Syntax_Syntax.rng = uu____4073;_},uu____4074)
        ->
        let uu____4093 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4093
    | uu____4094 ->
        ((let uu____4096 =
            let uu____4102 =
              let uu____4104 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____4104  in
            (FStar_Errors.Warning_NotEmbedded, uu____4102)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4096);
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
    let uu____4133 =
      let uu____4139 = FStar_Ident.range_of_id i  in
      let uu____4140 = FStar_Ident.string_of_id i  in
      (uu____4139, uu____4140)  in
    FStar_TypeChecker_NBETerm.embed repr cb uu____4133  in
  let unembed_ident cb t =
    let uu____4163 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____4163 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4187 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4187
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
    let uu____4197 =
      let uu____4205 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____4207 =
        let uu____4210 = fv_as_emb_typ range_fv  in
        let uu____4211 =
          let uu____4214 = fv_as_emb_typ string_fv  in [uu____4214]  in
        uu____4210 :: uu____4211  in
      (uu____4205, uu____4207)  in
    FStar_Syntax_Syntax.ET_app uu____4197  in
  let uu____4218 =
    let uu____4219 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____4220 =
      let uu____4227 =
        let uu____4232 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____4232  in
      let uu____4237 =
        let uu____4244 =
          let uu____4249 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____4249  in
        [uu____4244]  in
      uu____4227 :: uu____4237  in
    mkFV uu____4219 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____4220
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____4218 et 
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
    | FStar_Reflection_Data.Sg_Let (r,fv,univs,ty,t) ->
        let uu____4306 =
          let uu____4313 =
            let uu____4318 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____4318  in
          let uu____4320 =
            let uu____4327 =
              let uu____4332 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____4332  in
            let uu____4333 =
              let uu____4340 =
                let uu____4345 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs  in
                FStar_TypeChecker_NBETerm.as_arg uu____4345  in
              let uu____4348 =
                let uu____4355 =
                  let uu____4360 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4360  in
                let uu____4361 =
                  let uu____4368 =
                    let uu____4373 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4373  in
                  [uu____4368]  in
                uu____4355 :: uu____4361  in
              uu____4340 :: uu____4348  in
            uu____4327 :: uu____4333  in
          uu____4313 :: uu____4320  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____4306
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4400 =
          let uu____4407 =
            let uu____4412 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4412  in
          let uu____4416 =
            let uu____4423 =
              let uu____4428 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____4428  in
            [uu____4423]  in
          uu____4407 :: uu____4416  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____4400
    | FStar_Reflection_Data.Sg_Inductive (nm,univs,bs,t,dcs) ->
        let uu____4458 =
          let uu____4465 =
            let uu____4470 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4470  in
          let uu____4474 =
            let uu____4481 =
              let uu____4486 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs  in
              FStar_TypeChecker_NBETerm.as_arg uu____4486  in
            let uu____4489 =
              let uu____4496 =
                let uu____4501 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____4501  in
              let uu____4502 =
                let uu____4509 =
                  let uu____4514 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4514  in
                let uu____4515 =
                  let uu____4522 =
                    let uu____4527 =
                      let uu____4528 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____4528 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4527  in
                  [uu____4522]  in
                uu____4509 :: uu____4515  in
              uu____4496 :: uu____4502  in
            uu____4481 :: uu____4489  in
          uu____4465 :: uu____4474  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____4458
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4588,(dcs,uu____4590)::(t1,uu____4592)::(bs,uu____4594)::
         (us,uu____4596)::(nm,uu____4598)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____4633 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____4633
          (fun nm1  ->
             let uu____4651 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____4651
               (fun us1  ->
                  let uu____4665 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____4665
                    (fun bs1  ->
                       let uu____4671 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____4671
                         (fun t2  ->
                            let uu____4677 =
                              let uu____4685 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____4685 cb
                                dcs
                               in
                            FStar_Util.bind_opt uu____4677
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun uu____4715  ->
                                      FStar_Pervasives_Native.Some uu____4715)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4723,(t1,uu____4725)::(ty,uu____4727)::(univs,uu____4729)::
         (fvar,uu____4731)::(r,uu____4733)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____4768 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____4768
          (fun r1  ->
             let uu____4778 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar
                in
             FStar_Util.bind_opt uu____4778
               (fun fvar1  ->
                  let uu____4784 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs
                     in
                  FStar_Util.bind_opt uu____4784
                    (fun univs1  ->
                       let uu____4798 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____4798
                         (fun ty1  ->
                            let uu____4804 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____4804
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun uu____4811  ->
                                      FStar_Pervasives_Native.Some uu____4811)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar1, univs1, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4816,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4831 ->
        ((let uu____4833 =
            let uu____4839 =
              let uu____4841 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4841
               in
            (FStar_Errors.Warning_NotEmbedded, uu____4839)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4833);
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
        let uu____4864 =
          let uu____4871 =
            let uu____4876 =
              FStar_TypeChecker_NBETerm.mk_t
                (FStar_TypeChecker_NBETerm.Constant
                   (FStar_TypeChecker_NBETerm.Int i))
               in
            FStar_TypeChecker_NBETerm.as_arg uu____4876  in
          [uu____4871]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4864
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____4887 =
          let uu____4894 =
            let uu____4899 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4899  in
          let uu____4900 =
            let uu____4907 =
              let uu____4912 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4912  in
            [uu____4907]  in
          uu____4894 :: uu____4900  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4887
     in
  let rec unembed_exp cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4941,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4957,(i,uu____4959)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____4978 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____4978
          (fun i1  ->
             FStar_All.pipe_left
               (fun uu____4985  -> FStar_Pervasives_Native.Some uu____4985)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4987,(e2,uu____4989)::(e1,uu____4991)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____5014 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____5014
          (fun e11  ->
             let uu____5020 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____5020
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun uu____5027  ->
                       FStar_Pervasives_Native.Some uu____5027)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____5028 ->
        ((let uu____5030 =
            let uu____5036 =
              let uu____5038 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____5038  in
            (FStar_Errors.Warning_NotEmbedded, uu____5036)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5030);
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
  let embed rng lid =
    let uu____5067 = FStar_Ident.path_of_lid lid  in
    FStar_TypeChecker_NBETerm.embed e_string_list rng uu____5067  in
  let unembed cb t =
    let uu____5089 = FStar_TypeChecker_NBETerm.unembed e_string_list cb t  in
    FStar_Util.map_opt uu____5089
      (fun p  -> FStar_Ident.lid_of_path p FStar_Range.dummyRange)
     in
  let uu____5106 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____5111 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed unembed uu____5106 uu____5111 
let (e_qualifier :
  FStar_Reflection_Data.qualifier FStar_TypeChecker_NBETerm.embedding) =
  let embed cb q =
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
        let uu____5199 =
          let uu____5206 =
            let uu____5211 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____5211  in
          [uu____5206]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.fv
          [] uu____5199
    | FStar_Reflection_Data.Discriminator l ->
        let uu____5221 =
          let uu____5228 =
            let uu____5233 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____5233  in
          [uu____5228]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.fv
          [] uu____5221
    | FStar_Reflection_Data.Action l ->
        let uu____5243 =
          let uu____5250 =
            let uu____5255 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____5255  in
          [uu____5250]  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.fv []
          uu____5243
    | FStar_Reflection_Data.Projector (l,i) ->
        let uu____5266 =
          let uu____5273 =
            let uu____5278 = FStar_TypeChecker_NBETerm.embed e_lid cb l  in
            FStar_TypeChecker_NBETerm.as_arg uu____5278  in
          let uu____5279 =
            let uu____5286 =
              let uu____5291 = FStar_TypeChecker_NBETerm.embed e_ident cb i
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____5291  in
            [uu____5286]  in
          uu____5273 :: uu____5279  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.fv
          [] uu____5266
    | FStar_Reflection_Data.RecordType (ids1,ids2) ->
        let uu____5314 =
          let uu____5321 =
            let uu____5326 =
              let uu____5327 = FStar_TypeChecker_NBETerm.e_list e_ident  in
              FStar_TypeChecker_NBETerm.embed uu____5327 cb ids1  in
            FStar_TypeChecker_NBETerm.as_arg uu____5326  in
          let uu____5334 =
            let uu____5341 =
              let uu____5346 =
                let uu____5347 = FStar_TypeChecker_NBETerm.e_list e_ident  in
                FStar_TypeChecker_NBETerm.embed uu____5347 cb ids2  in
              FStar_TypeChecker_NBETerm.as_arg uu____5346  in
            [uu____5341]  in
          uu____5321 :: uu____5334  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.fv
          [] uu____5314
    | FStar_Reflection_Data.RecordConstructor (ids1,ids2) ->
        let uu____5376 =
          let uu____5383 =
            let uu____5388 =
              let uu____5389 = FStar_TypeChecker_NBETerm.e_list e_ident  in
              FStar_TypeChecker_NBETerm.embed uu____5389 cb ids1  in
            FStar_TypeChecker_NBETerm.as_arg uu____5388  in
          let uu____5396 =
            let uu____5403 =
              let uu____5408 =
                let uu____5409 = FStar_TypeChecker_NBETerm.e_list e_ident  in
                FStar_TypeChecker_NBETerm.embed uu____5409 cb ids2  in
              FStar_TypeChecker_NBETerm.as_arg uu____5408  in
            [uu____5403]  in
          uu____5383 :: uu____5396  in
        mkConstruct
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.fv
          [] uu____5376
     in
  let unembed cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5679)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
        ->
        let uu____5696 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5696
          (fun l1  ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Reflectable l1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5703)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
        ->
        let uu____5720 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5720
          (fun l1  ->
             FStar_Pervasives_Native.Some
               (FStar_Reflection_Data.Discriminator l1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(l,uu____5727)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
        ->
        let uu____5744 = FStar_TypeChecker_NBETerm.unembed e_lid cb l  in
        FStar_Util.bind_opt uu____5744
          (fun l1  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Action l1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,[],(i,uu____5751)::(l,uu____5753)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
        ->
        let uu____5774 = FStar_TypeChecker_NBETerm.unembed e_ident cb i  in
        FStar_Util.bind_opt uu____5774
          (fun i1  ->
             let uu____5780 = FStar_TypeChecker_NBETerm.unembed e_lid cb l
                in
             FStar_Util.bind_opt uu____5780
               (fun l1  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Projector (l1, i1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,[],(ids2,uu____5787)::(ids1,uu____5789)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
        ->
        let uu____5810 =
          let uu____5815 = FStar_TypeChecker_NBETerm.e_list e_ident  in
          FStar_TypeChecker_NBETerm.unembed uu____5815 cb ids1  in
        FStar_Util.bind_opt uu____5810
          (fun ids11  ->
             let uu____5829 =
               let uu____5834 = FStar_TypeChecker_NBETerm.e_list e_ident  in
               FStar_TypeChecker_NBETerm.unembed uu____5834 cb ids2  in
             FStar_Util.bind_opt uu____5829
               (fun ids21  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordType (ids11, ids21))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,[],(ids2,uu____5853)::(ids1,uu____5855)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
        ->
        let uu____5876 =
          let uu____5881 = FStar_TypeChecker_NBETerm.e_list e_ident  in
          FStar_TypeChecker_NBETerm.unembed uu____5881 cb ids1  in
        FStar_Util.bind_opt uu____5876
          (fun ids11  ->
             let uu____5895 =
               let uu____5900 = FStar_TypeChecker_NBETerm.e_list e_ident  in
               FStar_TypeChecker_NBETerm.unembed uu____5900 cb ids2  in
             FStar_Util.bind_opt uu____5895
               (fun ids21  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.RecordConstructor (ids11, ids21))))
    | uu____5917 ->
        ((let uu____5919 =
            let uu____5925 =
              let uu____5927 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded qualifier: %s" uu____5927
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5925)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5919);
         FStar_Pervasives_Native.None)
     in
  let uu____5931 =
    mkConstruct FStar_Reflection_Data.fstar_refl_qualifier_fv [] []  in
  let uu____5936 =
    fv_as_emb_typ FStar_Reflection_Data.fstar_refl_qualifier_fv  in
  FStar_TypeChecker_NBETerm.mk_emb embed unembed uu____5931 uu____5936 
let (e_qualifiers :
  FStar_Reflection_Data.qualifier Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_qualifier 