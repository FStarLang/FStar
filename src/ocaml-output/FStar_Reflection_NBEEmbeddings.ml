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
    let uu____78 =
      let uu____86 =
        FStar_Ident.string_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      (uu____86, [])  in
    FStar_Syntax_Syntax.ET_app uu____78
  
let mk_emb' :
  'Auu____100 .
    (FStar_TypeChecker_NBETerm.nbe_cbs ->
       'Auu____100 -> FStar_TypeChecker_NBETerm.t)
      ->
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_TypeChecker_NBETerm.t ->
           'Auu____100 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.fv ->
          'Auu____100 FStar_TypeChecker_NBETerm.embedding
  =
  fun x  ->
    fun y  ->
      fun fv  ->
        let uu____142 = mkFV fv [] []  in
        let uu____147 = fv_as_emb_typ fv  in
        FStar_TypeChecker_NBETerm.mk_emb x y uu____142 uu____147
  
let mk_lazy :
  'Auu____159 .
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      'Auu____159 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun cb  ->
    fun obj  ->
      fun ty  ->
        fun kind  ->
          let li =
            let uu____185 = FStar_Dyn.mkdyn obj  in
            {
              FStar_Syntax_Syntax.blob = uu____185;
              FStar_Syntax_Syntax.lkind = kind;
              FStar_Syntax_Syntax.ltyp = ty;
              FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
            }  in
          let thunk =
            FStar_Common.mk_thunk
              (fun uu____191  ->
                 let uu____192 = FStar_Syntax_Util.unfold_lazy li  in
                 FStar_TypeChecker_NBETerm.translate_cb cb uu____192)
             in
          FStar_TypeChecker_NBETerm.Lazy ((FStar_Util.Inl li), thunk)
  
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
           FStar_Syntax_Syntax.ltyp = uu____277;
           FStar_Syntax_Syntax.rng = uu____278;_},uu____279)
        ->
        let uu____298 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
          uu____298
    | uu____301 ->
        ((let uu____303 =
            let uu____309 =
              let uu____311 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____311  in
            (FStar_Errors.Warning_NotEmbedded, uu____309)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____303);
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
           FStar_Syntax_Syntax.ltyp = uu____345;
           FStar_Syntax_Syntax.rng = uu____346;_},uu____347)
        ->
        let uu____366 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____366
    | uu____367 ->
        ((let uu____369 =
            let uu____375 =
              let uu____377 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____377  in
            (FStar_Errors.Warning_NotEmbedded, uu____375)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____369);
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
          let uu____427 = f x  in
          FStar_Util.bind_opt uu____427
            (fun x1  ->
               let uu____435 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____435
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
      | uu____505 -> FStar_Pervasives_Native.None  in
    let uu____506 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    let uu____511 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____506;
      FStar_TypeChecker_NBETerm.emb_typ = uu____511
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
        let uu____544 =
          let uu____551 =
            let uu____556 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____556  in
          [uu____551]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____544
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____608)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____625 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____625
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____630 ->
        ((let uu____632 =
            let uu____638 =
              let uu____640 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____640  in
            (FStar_Errors.Warning_NotEmbedded, uu____638)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____632);
         FStar_Pervasives_Native.None)
     in
  let uu____644 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  let uu____649 = fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____644
    uu____649
  
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
           FStar_Syntax_Syntax.ltyp = uu____683;
           FStar_Syntax_Syntax.rng = uu____684;_},uu____685)
        ->
        let uu____704 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____704
    | uu____705 ->
        ((let uu____707 =
            let uu____713 =
              let uu____715 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____715  in
            (FStar_Errors.Warning_NotEmbedded, uu____713)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____707);
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
           FStar_Syntax_Syntax.ltyp = uu____749;
           FStar_Syntax_Syntax.rng = uu____750;_},uu____751)
        ->
        let uu____770 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____770
    | uu____771 ->
        ((let uu____773 =
            let uu____779 =
              let uu____781 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____781  in
            (FStar_Errors.Warning_NotEmbedded, uu____779)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____773);
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
           FStar_Syntax_Syntax.ltyp = uu____815;
           FStar_Syntax_Syntax.rng = uu____816;_},uu____817)
        ->
        let uu____836 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____836
    | uu____837 ->
        ((let uu____839 =
            let uu____845 =
              let uu____847 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____847  in
            (FStar_Errors.Warning_NotEmbedded, uu____845)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____839);
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
        let uu____878 =
          let uu____885 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____885]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____878
    | FStar_Reflection_Data.C_String s ->
        let uu____900 =
          let uu____907 =
            let uu____912 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____912  in
          [uu____907]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____900
    | FStar_Reflection_Data.C_Range r ->
        let uu____923 =
          let uu____930 =
            let uu____935 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_range cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____935  in
          [uu____930]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv []
          uu____923
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____1000)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____1017 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____1017
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____1026)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____1043 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____1043
          (fun s1  ->
             FStar_All.pipe_left
               (fun _0_3  -> FStar_Pervasives_Native.Some _0_3)
               (FStar_Reflection_Data.C_String s1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(r,uu____1056)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
        ->
        let uu____1073 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range
            cb r
           in
        FStar_Util.bind_opt uu____1073
          (fun r1  ->
             FStar_All.pipe_left
               (fun _0_4  -> FStar_Pervasives_Native.Some _0_4)
               (FStar_Reflection_Data.C_Range r1))
    | uu____1080 ->
        ((let uu____1082 =
            let uu____1088 =
              let uu____1090 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____1090  in
            (FStar_Errors.Warning_NotEmbedded, uu____1088)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____1082);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst_fv
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____1101  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1114 =
            let uu____1121 =
              let uu____1126 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1126  in
            [uu____1121]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____1114
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1141 =
            let uu____1148 =
              let uu____1153 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1153  in
            let uu____1154 =
              let uu____1161 =
                let uu____1166 =
                  let uu____1167 =
                    let uu____1172 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____1172  in
                  FStar_TypeChecker_NBETerm.embed uu____1167 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____1166  in
              [uu____1161]  in
            uu____1148 :: uu____1154  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1141
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1190 =
            let uu____1197 =
              let uu____1202 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1202  in
            [uu____1197]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1190
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1212 =
            let uu____1219 =
              let uu____1224 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1224  in
            [uu____1219]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1212
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1235 =
            let uu____1242 =
              let uu____1247 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1247  in
            let uu____1248 =
              let uu____1255 =
                let uu____1260 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1260  in
              [uu____1255]  in
            uu____1242 :: uu____1248  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1235
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____1290)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1307 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____1307
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_5  -> FStar_Pervasives_Native.Some _0_5)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____1316)::(f,uu____1318)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1339 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____1339
            (fun f1  ->
               let uu____1345 =
                 let uu____1350 =
                   let uu____1355 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____1355  in
                 FStar_TypeChecker_NBETerm.unembed uu____1350 cb ps  in
               FStar_Util.bind_opt uu____1345
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _0_6  -> FStar_Pervasives_Native.Some _0_6)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1372)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1389 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1389
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_7  -> FStar_Pervasives_Native.Some _0_7)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1398)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1415 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1415
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_8  -> FStar_Pervasives_Native.Some _0_8)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____1424)::(bv,uu____1426)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1447 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1447
            (fun bv1  ->
               let uu____1453 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____1453
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_9  -> FStar_Pervasives_Native.Some _0_9)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1460 ->
          ((let uu____1462 =
              let uu____1468 =
                let uu____1470 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1470
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1468)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1462);
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
    let uu____1511 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1511
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1542 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1542 e_aqualv
  
let rec unlazy_as_t :
  'Auu____1552 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1552
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Util.Inl
           { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
             FStar_Syntax_Syntax.ltyp = uu____1565;
             FStar_Syntax_Syntax.rng = uu____1566;_},uu____1567)
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1586 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1624 =
            let uu____1631 =
              let uu____1636 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1636  in
            [uu____1631]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1624
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1646 =
            let uu____1653 =
              let uu____1658 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1658  in
            [uu____1653]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1646
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1668 =
            let uu____1675 =
              let uu____1680 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1680  in
            [uu____1675]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1668
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1691 =
            let uu____1698 =
              let uu____1703 =
                let uu____1704 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1704 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1703  in
            let uu____1707 =
              let uu____1714 =
                let uu____1719 =
                  let uu____1720 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1720 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1719  in
              [uu____1714]  in
            uu____1698 :: uu____1707  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1691
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1745 =
            let uu____1752 =
              let uu____1757 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1757  in
            let uu____1758 =
              let uu____1765 =
                let uu____1770 =
                  let uu____1771 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1771 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1770  in
              [uu____1765]  in
            uu____1752 :: uu____1758  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1745
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1788 =
            let uu____1795 =
              let uu____1800 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1800  in
            let uu____1801 =
              let uu____1808 =
                let uu____1813 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1813  in
              [uu____1808]  in
            uu____1795 :: uu____1801  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1788
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1827 =
            let uu____1834 =
              let uu____1839 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1839  in
            [uu____1834]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1827
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____1850 =
            let uu____1857 =
              let uu____1862 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1862  in
            let uu____1863 =
              let uu____1870 =
                let uu____1875 =
                  let uu____1876 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1876 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1875  in
              [uu____1870]  in
            uu____1857 :: uu____1863  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1850
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1892 =
            let uu____1899 =
              let uu____1904 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1904  in
            [uu____1899]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1892
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____1915 =
            let uu____1922 =
              let uu____1927 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1927  in
            let uu____1928 =
              let uu____1935 =
                let uu____1940 =
                  mk_lazy cb (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1940  in
              [uu____1935]  in
            uu____1922 :: uu____1928  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____1915
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1963 =
            let uu____1970 =
              let uu____1975 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1975  in
            let uu____1977 =
              let uu____1984 =
                let uu____1989 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1989  in
              let uu____1990 =
                let uu____1997 =
                  let uu____2002 =
                    let uu____2003 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____2003 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2002  in
                let uu____2006 =
                  let uu____2013 =
                    let uu____2018 =
                      let uu____2019 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____2019 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____2018  in
                  [uu____2013]  in
                uu____1997 :: uu____2006  in
              uu____1984 :: uu____1990  in
            uu____1970 :: uu____1977  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____1963
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____2048 =
            let uu____2055 =
              let uu____2060 =
                let uu____2061 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2061 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____2060  in
            let uu____2064 =
              let uu____2071 =
                let uu____2076 =
                  let uu____2077 =
                    let uu____2086 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____2086  in
                  FStar_TypeChecker_NBETerm.embed uu____2077 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2076  in
              [uu____2071]  in
            uu____2055 :: uu____2064  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2048
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____2122 =
            let uu____2129 =
              let uu____2134 =
                let uu____2135 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2135 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2134  in
            let uu____2138 =
              let uu____2145 =
                let uu____2150 =
                  let uu____2151 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2151 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2150  in
              let uu____2154 =
                let uu____2161 =
                  let uu____2166 =
                    let uu____2167 =
                      let uu____2172 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2172  in
                    FStar_TypeChecker_NBETerm.embed uu____2167 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2166  in
                [uu____2161]  in
              uu____2145 :: uu____2154  in
            uu____2129 :: uu____2138  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2122
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2200 =
            let uu____2207 =
              let uu____2212 =
                let uu____2213 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2213 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2212  in
            let uu____2216 =
              let uu____2223 =
                let uu____2228 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2228  in
              let uu____2229 =
                let uu____2236 =
                  let uu____2241 =
                    let uu____2242 =
                      let uu____2247 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2247  in
                    FStar_TypeChecker_NBETerm.embed uu____2242 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2241  in
                [uu____2236]  in
              uu____2223 :: uu____2229  in
            uu____2207 :: uu____2216  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2200
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2288,(b,uu____2290)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2309 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2309
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_10  -> FStar_Pervasives_Native.Some _0_10)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2317,(b,uu____2319)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2338 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2338
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_11  -> FStar_Pervasives_Native.Some _0_11)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2346,(f,uu____2348)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2367 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____2367
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _0_12  -> FStar_Pervasives_Native.Some _0_12)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2375,(r,uu____2377)::(l,uu____2379)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2402 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____2402
            (fun l1  ->
               let uu____2408 = FStar_TypeChecker_NBETerm.unembed e_argv cb r
                  in
               FStar_Util.bind_opt uu____2408
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _0_13  -> FStar_Pervasives_Native.Some _0_13)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2416,(t1,uu____2418)::(b,uu____2420)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2443 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2443
            (fun b1  ->
               let uu____2449 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2449
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2457,(t1,uu____2459)::(b,uu____2461)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2484 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2484
            (fun b1  ->
               let uu____2490 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____2490
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2498,(u,uu____2500)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2519 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____2519
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2527,(t1,uu____2529)::(b,uu____2531)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2554 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2554
            (fun b1  ->
               let uu____2560 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2560
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2568,(c,uu____2570)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2589 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____2589
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2597,(l,uu____2599)::(u,uu____2601)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2624 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____2624
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2634,(t2,uu____2636)::(t1,uu____2638)::(b,uu____2640)::
           (r,uu____2642)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2673 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____2673
            (fun r1  ->
               let uu____2683 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____2683
                 (fun b1  ->
                    let uu____2689 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____2689
                      (fun t11  ->
                         let uu____2695 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____2695
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _0_20  ->
                                   FStar_Pervasives_Native.Some _0_20)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2704,(brs,uu____2706)::(t1,uu____2708)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2731 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
          FStar_Util.bind_opt uu____2731
            (fun t2  ->
               let uu____2737 =
                 let uu____2742 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2742 cb brs  in
               FStar_Util.bind_opt uu____2737
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2760,(tacopt,uu____2762)::(t1,uu____2764)::(e,uu____2766)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2793 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____2793
            (fun e1  ->
               let uu____2799 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2799
                 (fun t2  ->
                    let uu____2805 =
                      let uu____2810 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2810 cb tacopt
                       in
                    FStar_Util.bind_opt uu____2805
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2828,(tacopt,uu____2830)::(c,uu____2832)::(e,uu____2834)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____2861 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____2861
            (fun e1  ->
               let uu____2867 = FStar_TypeChecker_NBETerm.unembed e_comp cb c
                  in
               FStar_Util.bind_opt uu____2867
                 (fun c1  ->
                    let uu____2873 =
                      let uu____2878 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2878 cb tacopt
                       in
                    FStar_Util.bind_opt uu____2873
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____2896,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
            FStar_Reflection_Data.Tv_Unknown
      | uu____2913 ->
          ((let uu____2915 =
              let uu____2921 =
                let uu____2923 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____2923
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2921)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2915);
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
    let uu____2950 =
      let uu____2957 =
        let uu____2962 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____2962  in
      let uu____2964 =
        let uu____2971 =
          let uu____2976 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____2976  in
        let uu____2977 =
          let uu____2984 =
            let uu____2989 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2989  in
          [uu____2984]  in
        uu____2971 :: uu____2977  in
      uu____2957 :: uu____2964  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____2950
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3022,(s,uu____3024)::(idx,uu____3026)::(nm,uu____3028)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____3055 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____3055
          (fun nm1  ->
             let uu____3065 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____3065
               (fun idx1  ->
                  let uu____3071 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____3071
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____3078 ->
        ((let uu____3080 =
            let uu____3086 =
              let uu____3088 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3088  in
            (FStar_Errors.Warning_NotEmbedded, uu____3086)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3080);
         FStar_Pervasives_Native.None)
     in
  mk_emb' embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view_fv
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____3112 =
          let uu____3119 =
            let uu____3124 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3124  in
          let uu____3125 =
            let uu____3132 =
              let uu____3137 =
                let uu____3138 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____3138 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3137  in
            [uu____3132]  in
          uu____3119 :: uu____3125  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3112
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3162 =
          let uu____3169 =
            let uu____3174 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3174  in
          let uu____3175 =
            let uu____3182 =
              let uu____3187 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3187  in
            [uu____3182]  in
          uu____3169 :: uu____3175  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3162
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3220,(md,uu____3222)::(t1,uu____3224)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3247 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3247
          (fun t2  ->
             let uu____3253 =
               let uu____3258 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3258 cb md  in
             FStar_Util.bind_opt uu____3253
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3276,(post,uu____3278)::(pre,uu____3280)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3303 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____3303
          (fun pre1  ->
             let uu____3309 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____3309
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3317,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
          FStar_Reflection_Data.C_Unknown
    | uu____3334 ->
        ((let uu____3336 =
            let uu____3342 =
              let uu____3344 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3344
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3342)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3336);
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
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3390,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3406,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3422,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____3437 ->
        ((let uu____3439 =
            let uu____3445 =
              let uu____3447 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____3447  in
            (FStar_Errors.Warning_NotEmbedded, uu____3445)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3439);
         FStar_Pervasives_Native.None)
     in
  let uu____3451 =
    FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
      FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
     in
  mk_emb' embed_order unembed_order uu____3451 
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
           FStar_Syntax_Syntax.ltyp = uu____3482;
           FStar_Syntax_Syntax.rng = uu____3483;_},uu____3484)
        ->
        let uu____3503 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____3503
    | uu____3504 ->
        ((let uu____3506 =
            let uu____3512 =
              let uu____3514 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3514  in
            (FStar_Errors.Warning_NotEmbedded, uu____3512)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3506);
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
    let uu____3543 =
      let uu____3549 = FStar_Ident.range_of_id i  in
      let uu____3550 = FStar_Ident.text_of_id i  in (uu____3549, uu____3550)
       in
    FStar_TypeChecker_NBETerm.embed repr cb uu____3543  in
  let unembed_ident cb t =
    let uu____3573 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____3573 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____3597 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____3597
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
    let uu____3607 =
      let uu____3615 =
        FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2  in
      let uu____3617 =
        let uu____3620 = fv_as_emb_typ range_fv  in
        let uu____3621 =
          let uu____3624 = fv_as_emb_typ string_fv  in [uu____3624]  in
        uu____3620 :: uu____3621  in
      (uu____3615, uu____3617)  in
    FStar_Syntax_Syntax.ET_app uu____3607  in
  let uu____3628 =
    let uu____3629 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____3630 =
      let uu____3637 =
        let uu____3642 = mkFV range_fv [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____3642  in
      let uu____3647 =
        let uu____3654 =
          let uu____3659 = mkFV string_fv [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____3659  in
        [uu____3654]  in
      uu____3637 :: uu____3647  in
    mkFV uu____3629 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____3630
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3628 et 
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
        let uu____3716 =
          let uu____3723 =
            let uu____3728 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3728  in
          let uu____3730 =
            let uu____3737 =
              let uu____3742 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3742  in
            let uu____3743 =
              let uu____3750 =
                let uu____3755 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____3755  in
              let uu____3758 =
                let uu____3765 =
                  let uu____3770 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____3770  in
                let uu____3771 =
                  let uu____3778 =
                    let uu____3783 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____3783  in
                  [uu____3778]  in
                uu____3765 :: uu____3771  in
              uu____3750 :: uu____3758  in
            uu____3737 :: uu____3743  in
          uu____3723 :: uu____3730  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____3716
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3810 =
          let uu____3817 =
            let uu____3822 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____3822  in
          let uu____3826 =
            let uu____3833 =
              let uu____3838 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____3838  in
            [uu____3833]  in
          uu____3817 :: uu____3826  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____3810
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____3868 =
          let uu____3875 =
            let uu____3880 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____3880  in
          let uu____3884 =
            let uu____3891 =
              let uu____3896 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3896  in
            let uu____3899 =
              let uu____3906 =
                let uu____3911 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____3911  in
              let uu____3912 =
                let uu____3919 =
                  let uu____3924 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____3924  in
                let uu____3925 =
                  let uu____3932 =
                    let uu____3937 =
                      let uu____3938 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____3938 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____3937  in
                  [uu____3932]  in
                uu____3919 :: uu____3925  in
              uu____3906 :: uu____3912  in
            uu____3891 :: uu____3899  in
          uu____3875 :: uu____3884  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____3868
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3998,(dcs,uu____4000)::(t1,uu____4002)::(bs,uu____4004)::
         (us,uu____4006)::(nm,uu____4008)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____4043 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____4043
          (fun nm1  ->
             let uu____4061 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____4061
               (fun us1  ->
                  let uu____4075 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____4075
                    (fun bs1  ->
                       let uu____4081 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____4081
                         (fun t2  ->
                            let uu____4087 =
                              let uu____4095 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____4095 cb
                                dcs
                               in
                            FStar_Util.bind_opt uu____4087
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_29  ->
                                      FStar_Pervasives_Native.Some _0_29)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4132,(t1,uu____4134)::(ty,uu____4136)::(univs1,uu____4138)::
         (fvar1,uu____4140)::(r,uu____4142)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____4177 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____4177
          (fun r1  ->
             let uu____4187 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1
                in
             FStar_Util.bind_opt uu____4187
               (fun fvar2  ->
                  let uu____4193 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____4193
                    (fun univs2  ->
                       let uu____4207 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____4207
                         (fun ty1  ->
                            let uu____4213 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____4213
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _0_30  ->
                                      FStar_Pervasives_Native.Some _0_30)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4224,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4239 ->
        ((let uu____4241 =
            let uu____4247 =
              let uu____4249 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4249
               in
            (FStar_Errors.Warning_NotEmbedded, uu____4247)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4241);
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
        let uu____4272 =
          let uu____4279 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____4279]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4272
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____4294 =
          let uu____4301 =
            let uu____4306 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4306  in
          let uu____4307 =
            let uu____4314 =
              let uu____4319 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4319  in
            [uu____4314]  in
          uu____4301 :: uu____4307  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4294
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4348,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4364,(i,uu____4366)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____4385 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____4385
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4393,(e2,uu____4395)::(e1,uu____4397)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____4420 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____4420
          (fun e11  ->
             let uu____4426 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____4426
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____4433 ->
        ((let uu____4435 =
            let uu____4441 =
              let uu____4443 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4443  in
            (FStar_Errors.Warning_NotEmbedded, uu____4441)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4435);
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