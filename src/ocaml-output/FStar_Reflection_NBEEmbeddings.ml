open Prims
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (FStar_TypeChecker_NBETerm.t,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
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
      (FStar_TypeChecker_NBETerm.t,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_NBETerm.t)
  =
  fun fv  ->
    fun us  ->
      fun ts  ->
        FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us)
          (FStar_List.rev ts)
  
let mk_lazy :
  'Auu____79 .
    'Auu____79 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun obj  ->
    fun ty  ->
      fun kind  ->
        let li =
          let uu____100 = FStar_Dyn.mkdyn obj  in
          {
            FStar_Syntax_Syntax.blob = uu____100;
            FStar_Syntax_Syntax.lkind = kind;
            FStar_Syntax_Syntax.ltyp = ty;
            FStar_Syntax_Syntax.rng = FStar_Range.dummyRange
          }  in
        FStar_TypeChecker_NBETerm.Lazy li
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv cb bv =
    mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv
     in
  let unembed_bv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____150;
          FStar_Syntax_Syntax.rng = uu____151;_}
        ->
        let uu____154 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____154
    | uu____157 ->
        ((let uu____159 =
            let uu____164 =
              let uu____165 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____165  in
            (FStar_Errors.Warning_NotEmbedded, uu____164)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____159);
         FStar_Pervasives_Native.None)
     in
  let uu____166 = mkFV FStar_Reflection_Data.fstar_refl_bv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_bv unembed_bv uu____166 
let (e_binder :
  FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding) =
  let embed_binder cb b =
    mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder
     in
  let unembed_binder cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____220;
          FStar_Syntax_Syntax.rng = uu____221;_}
        ->
        let uu____224 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____224
    | uu____225 ->
        ((let uu____227 =
            let uu____232 =
              let uu____233 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____233  in
            (FStar_Errors.Warning_NotEmbedded, uu____232)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____227);
         FStar_Pervasives_Native.None)
     in
  let uu____234 = mkFV FStar_Reflection_Data.fstar_refl_binder_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_binder unembed_binder uu____234 
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
          let uu____284 = f x  in
          FStar_Util.bind_opt uu____284
            (fun x1  ->
               let uu____292 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____292
                 (fun xs1  -> FStar_Pervasives_Native.Some (x1 :: xs1)))
  
let (e_term_aq :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 Prims.list ->
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
      | uu____381 -> FStar_Pervasives_Native.None  in
    let uu____382 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____382
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
        let uu____427 =
          let uu____434 =
            let uu____439 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____439  in
          [uu____434]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____427
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____505)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____522 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____522
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____531 ->
        ((let uu____533 =
            let uu____538 =
              let uu____539 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____539  in
            (FStar_Errors.Warning_NotEmbedded, uu____538)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____533);
         FStar_Pervasives_Native.None)
     in
  let uu____540 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____540 
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_list e_binder 
let (e_fv : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding) =
  let embed_fv cb fv =
    mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar
     in
  let unembed_fv cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____596;
          FStar_Syntax_Syntax.rng = uu____597;_}
        ->
        let uu____600 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____600
    | uu____601 ->
        ((let uu____603 =
            let uu____608 =
              let uu____609 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____609  in
            (FStar_Errors.Warning_NotEmbedded, uu____608)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____603);
         FStar_Pervasives_Native.None)
     in
  let uu____610 = mkFV FStar_Reflection_Data.fstar_refl_fv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_fv unembed_fv uu____610 
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp cb c =
    mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp
     in
  let unembed_comp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____664;
          FStar_Syntax_Syntax.rng = uu____665;_}
        ->
        let uu____668 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____668
    | uu____669 ->
        ((let uu____671 =
            let uu____676 =
              let uu____677 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____677  in
            (FStar_Errors.Warning_NotEmbedded, uu____676)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____671);
         FStar_Pervasives_Native.None)
     in
  let uu____678 = mkFV FStar_Reflection_Data.fstar_refl_comp_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp unembed_comp uu____678 
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env cb e =
    mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env
     in
  let unembed_env cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____732;
          FStar_Syntax_Syntax.rng = uu____733;_}
        ->
        let uu____736 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____736
    | uu____737 ->
        ((let uu____739 =
            let uu____744 =
              let uu____745 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____745  in
            (FStar_Errors.Warning_NotEmbedded, uu____744)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____739);
         FStar_Pervasives_Native.None)
     in
  let uu____746 = mkFV FStar_Reflection_Data.fstar_refl_env_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_env unembed_env uu____746 
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
        let uu____787 =
          let uu____794 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____794]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____787
    | FStar_Reflection_Data.C_String s ->
        let uu____808 =
          let uu____815 =
            let uu____820 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____820  in
          [uu____815]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____808
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____899)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____916 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____916
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____929)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____946 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____946
          (fun s1  ->
             FStar_All.pipe_left
               (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
               (FStar_Reflection_Data.C_String s1))
    | uu____957 ->
        ((let uu____959 =
            let uu____964 =
              let uu____965 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____965  in
            (FStar_Errors.Warning_NotEmbedded, uu____964)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____959);
         FStar_Pervasives_Native.None)
     in
  let uu____966 = mkFV FStar_Reflection_Data.fstar_refl_vconst_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_const unembed_const uu____966 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____977  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1000 =
            let uu____1007 =
              let uu____1012 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1012  in
            [uu____1007]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____1000
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1031 =
            let uu____1038 =
              let uu____1043 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1043  in
            let uu____1048 =
              let uu____1055 =
                let uu____1060 =
                  let uu____1061 =
                    let uu____1066 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____1066  in
                  FStar_TypeChecker_NBETerm.embed uu____1061 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____1060  in
              [uu____1055]  in
            uu____1038 :: uu____1048  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1031
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1088 =
            let uu____1095 =
              let uu____1100 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1100  in
            [uu____1095]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1088
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1114 =
            let uu____1121 =
              let uu____1126 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1126  in
            [uu____1121]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1114
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1141 =
            let uu____1148 =
              let uu____1153 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1153  in
            let uu____1158 =
              let uu____1165 =
                let uu____1170 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1170  in
              [uu____1165]  in
            uu____1148 :: uu____1158  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1141
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____1214)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1231 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____1231
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____1244)::(f,uu____1246)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1267 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____1267
            (fun f1  ->
               let uu____1277 =
                 let uu____1282 =
                   let uu____1287 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____1287  in
                 FStar_TypeChecker_NBETerm.unembed uu____1282 cb ps  in
               FStar_Util.bind_opt uu____1277
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1308)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1325 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1325
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1338)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1355 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1355
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____1368)::(bv,uu____1370)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1391 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1391
            (fun bv1  ->
               let uu____1401 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____1401
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1412 ->
          ((let uu____1414 =
              let uu____1419 =
                let uu____1420 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1420
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1419)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1414);
           FStar_Pervasives_Native.None)
       in
    let uu____1421 = mkFV FStar_Reflection_Data.fstar_refl_pattern_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_pattern unembed_pattern uu____1421
  
let (e_pattern :
  FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding) =
  e_pattern' () 
let (e_branch :
  FStar_Reflection_Data.branch FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_pattern e_term 
let (e_argv : FStar_Reflection_Data.argv FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_tuple2 e_term e_aqualv 
let (e_branch_aq :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1459 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1459
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1489 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1489 e_aqualv
  
let rec unlazy_as_t :
  'Auu____1498 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1498
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____1511;
            FStar_Syntax_Syntax.rng = uu____1512;_}
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1515 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1561 =
            let uu____1568 =
              let uu____1573 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1573  in
            [uu____1568]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1561
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1587 =
            let uu____1594 =
              let uu____1599 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1599  in
            [uu____1594]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1587
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1613 =
            let uu____1620 =
              let uu____1625 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1625  in
            [uu____1620]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1613
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1640 =
            let uu____1647 =
              let uu____1652 =
                let uu____1653 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1653 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1652  in
            let uu____1660 =
              let uu____1667 =
                let uu____1672 =
                  let uu____1673 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1673 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1672  in
              [uu____1667]  in
            uu____1647 :: uu____1660  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1640
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1702 =
            let uu____1709 =
              let uu____1714 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1714  in
            let uu____1719 =
              let uu____1726 =
                let uu____1731 =
                  let uu____1732 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1732 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1731  in
              [uu____1726]  in
            uu____1709 :: uu____1719  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1702
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1753 =
            let uu____1760 =
              let uu____1765 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1765  in
            let uu____1770 =
              let uu____1777 =
                let uu____1782 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1782  in
              [uu____1777]  in
            uu____1760 :: uu____1770  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1753
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1800 =
            let uu____1807 =
              let uu____1812 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1812  in
            [uu____1807]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1800
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____1827 =
            let uu____1834 =
              let uu____1839 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1839  in
            let uu____1844 =
              let uu____1851 =
                let uu____1856 =
                  let uu____1857 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1857 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1856  in
              [uu____1851]  in
            uu____1834 :: uu____1844  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1827
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1877 =
            let uu____1884 =
              let uu____1889 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1889  in
            [uu____1884]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1877
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____1904 =
            let uu____1911 =
              let uu____1916 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1916  in
            let uu____1921 =
              let uu____1928 =
                let uu____1933 =
                  mk_lazy (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1933  in
              [uu____1928]  in
            uu____1911 :: uu____1921  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____1904
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1954 =
            let uu____1961 =
              let uu____1966 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1966  in
            let uu____1971 =
              let uu____1978 =
                let uu____1983 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1983  in
              let uu____1988 =
                let uu____1995 =
                  let uu____2000 =
                    let uu____2001 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____2001 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2000  in
                let uu____2008 =
                  let uu____2015 =
                    let uu____2020 =
                      let uu____2021 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____2021 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____2020  in
                  [uu____2015]  in
                uu____1995 :: uu____2008  in
              uu____1978 :: uu____1988  in
            uu____1961 :: uu____1971  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____1954
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____2054 =
            let uu____2061 =
              let uu____2066 =
                let uu____2067 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2067 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____2066  in
            let uu____2074 =
              let uu____2081 =
                let uu____2086 =
                  let uu____2087 =
                    let uu____2096 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____2096  in
                  FStar_TypeChecker_NBETerm.embed uu____2087 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2086  in
              [uu____2081]  in
            uu____2061 :: uu____2074  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2054
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____2136 =
            let uu____2143 =
              let uu____2148 =
                let uu____2149 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2149 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2148  in
            let uu____2156 =
              let uu____2163 =
                let uu____2168 =
                  let uu____2169 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2169 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2168  in
              let uu____2176 =
                let uu____2183 =
                  let uu____2188 =
                    let uu____2189 =
                      let uu____2194 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2194  in
                    FStar_TypeChecker_NBETerm.embed uu____2189 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2188  in
                [uu____2183]  in
              uu____2163 :: uu____2176  in
            uu____2143 :: uu____2156  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2136
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2226 =
            let uu____2233 =
              let uu____2238 =
                let uu____2239 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2239 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2238  in
            let uu____2246 =
              let uu____2253 =
                let uu____2258 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2258  in
              let uu____2263 =
                let uu____2270 =
                  let uu____2275 =
                    let uu____2276 =
                      let uu____2281 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2281  in
                    FStar_TypeChecker_NBETerm.embed uu____2276 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2275  in
                [uu____2270]  in
              uu____2253 :: uu____2263  in
            uu____2233 :: uu____2246  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2226
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2336,(b,uu____2338)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2357 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2357
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2369,(b,uu____2371)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2390 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2390
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2402,(f,uu____2404)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2423 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____2423
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2435,(r,uu____2437)::(l,uu____2439)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2462 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____2462
            (fun l1  ->
               let uu____2472 = FStar_TypeChecker_NBETerm.unembed e_argv cb r
                  in
               FStar_Util.bind_opt uu____2472
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2484,(t1,uu____2486)::(b,uu____2488)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2511 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2511
            (fun b1  ->
               let uu____2521 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2521
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2533,(t1,uu____2535)::(b,uu____2537)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2560 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2560
            (fun b1  ->
               let uu____2570 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____2570
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2582,(u,uu____2584)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2603 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____2603
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2615,(t1,uu____2617)::(b,uu____2619)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2642 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2642
            (fun b1  ->
               let uu____2652 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2652
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2664,(c,uu____2666)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2685 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____2685
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2697,(l,uu____2699)::(u,uu____2701)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2724 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____2724
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2738,(t2,uu____2740)::(t1,uu____2742)::(b,uu____2744)::
           (r,uu____2746)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2777 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____2777
            (fun r1  ->
               let uu____2787 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____2787
                 (fun b1  ->
                    let uu____2797 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____2797
                      (fun t11  ->
                         let uu____2807 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____2807
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _0_34  ->
                                   FStar_Pervasives_Native.Some _0_34)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2819,(brs,uu____2821)::(t1,uu____2823)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2846 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
          FStar_Util.bind_opt uu____2846
            (fun t2  ->
               let uu____2856 =
                 let uu____2861 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2861 cb brs  in
               FStar_Util.bind_opt uu____2856
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2883,(tacopt,uu____2885)::(t1,uu____2887)::(e,uu____2889)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2916 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____2916
            (fun e1  ->
               let uu____2926 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2926
                 (fun t2  ->
                    let uu____2936 =
                      let uu____2941 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2941 cb tacopt
                       in
                    FStar_Util.bind_opt uu____2936
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2963,(tacopt,uu____2965)::(c,uu____2967)::(e,uu____2969)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____2996 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____2996
            (fun e1  ->
               let uu____3006 = FStar_TypeChecker_NBETerm.unembed e_comp cb c
                  in
               FStar_Util.bind_opt uu____3006
                 (fun c1  ->
                    let uu____3016 =
                      let uu____3021 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3021 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3016
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____3043,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
            FStar_Reflection_Data.Tv_Unknown
      | uu____3060 ->
          ((let uu____3062 =
              let uu____3067 =
                let uu____3068 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____3068
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3067)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3062);
           FStar_Pervasives_Native.None)
       in
    let uu____3069 = mkFV FStar_Reflection_Data.fstar_refl_term_view_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_term_view unembed_term_view
      uu____3069
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view cb bvv =
    let uu____3105 =
      let uu____3112 =
        let uu____3117 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____3117  in
      let uu____3122 =
        let uu____3129 =
          let uu____3134 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____3134  in
        let uu____3139 =
          let uu____3146 =
            let uu____3151 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3151  in
          [uu____3146]  in
        uu____3129 :: uu____3139  in
      uu____3112 :: uu____3122  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____3105
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3198,(s,uu____3200)::(idx,uu____3202)::(nm,uu____3204)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____3231 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____3231
          (fun nm1  ->
             let uu____3241 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____3241
               (fun idx1  ->
                  let uu____3251 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____3251
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____3262 ->
        ((let uu____3264 =
            let uu____3269 =
              let uu____3270 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3270  in
            (FStar_Errors.Warning_NotEmbedded, uu____3269)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3264);
         FStar_Pervasives_Native.None)
     in
  let uu____3271 = mkFV FStar_Reflection_Data.fstar_refl_bv_view_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_bv_view unembed_bv_view uu____3271 
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____3305 =
          let uu____3312 =
            let uu____3317 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3317  in
          let uu____3322 =
            let uu____3329 =
              let uu____3334 =
                let uu____3335 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____3335 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3334  in
            [uu____3329]  in
          uu____3312 :: uu____3322  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3305
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3363 =
          let uu____3370 =
            let uu____3375 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3375  in
          let uu____3380 =
            let uu____3387 =
              let uu____3392 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3392  in
            [uu____3387]  in
          uu____3370 :: uu____3380  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3363
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3439,(md,uu____3441)::(t1,uu____3443)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3466 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3466
          (fun t2  ->
             let uu____3476 =
               let uu____3481 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3481 cb md  in
             FStar_Util.bind_opt uu____3476
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3503,(post,uu____3505)::(pre,uu____3507)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3530 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____3530
          (fun pre1  ->
             let uu____3540 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____3540
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3552,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
          FStar_Reflection_Data.C_Unknown
    | uu____3569 ->
        ((let uu____3571 =
            let uu____3576 =
              let uu____3577 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3577
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3576)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3571);
         FStar_Pervasives_Native.None)
     in
  let uu____3578 = mkFV FStar_Reflection_Data.fstar_refl_comp_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp_view unembed_comp_view
    uu____3578
  
let (e_order : FStar_Order.order FStar_TypeChecker_NBETerm.embedding) =
  let embed_order cb o =
    match o with
    | FStar_Order.Lt  -> mkConstruct FStar_Reflection_Data.ord_Lt_fv [] []
    | FStar_Order.Eq  -> mkConstruct FStar_Reflection_Data.ord_Eq_fv [] []
    | FStar_Order.Gt  -> mkConstruct FStar_Reflection_Data.ord_Gt_fv [] []
     in
  let unembed_order cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3644,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3660,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3676,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____3691 ->
        ((let uu____3693 =
            let uu____3698 =
              let uu____3699 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____3699  in
            (FStar_Errors.Warning_NotEmbedded, uu____3698)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3693);
         FStar_Pervasives_Native.None)
     in
  let uu____3700 =
    let uu____3701 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____3701 [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_order unembed_order uu____3700 
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt cb se =
    mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt
     in
  let unembed_sigelt cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____3755;
          FStar_Syntax_Syntax.rng = uu____3756;_}
        ->
        let uu____3759 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____3759
    | uu____3760 ->
        ((let uu____3762 =
            let uu____3767 =
              let uu____3768 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3768  in
            (FStar_Errors.Warning_NotEmbedded, uu____3767)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3762);
         FStar_Pervasives_Native.None)
     in
  let uu____3769 = mkFV FStar_Reflection_Data.fstar_refl_sigelt_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt unembed_sigelt uu____3769 
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string
     in
  let embed_ident cb i =
    let uu____3806 =
      let uu____3811 = FStar_Ident.range_of_id i  in
      let uu____3812 = FStar_Ident.text_of_id i  in (uu____3811, uu____3812)
       in
    FStar_TypeChecker_NBETerm.embed repr cb uu____3806  in
  let unembed_ident cb t =
    let uu____3846 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____3846 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____3869 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____3869
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____3874 =
    let uu____3875 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____3876 =
      let uu____3883 =
        let uu____3888 =
          let uu____3889 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          mkFV uu____3889 [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____3888  in
      let uu____3894 =
        let uu____3901 =
          let uu____3906 =
            let uu____3907 =
              FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            mkFV uu____3907 [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____3906  in
        [uu____3901]  in
      uu____3883 :: uu____3894  in
    mkFV uu____3875 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____3876
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3874 
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
        let uu____3966 =
          let uu____3973 =
            let uu____3978 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3978  in
          let uu____3983 =
            let uu____3990 =
              let uu____3995 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3995  in
            let uu____4000 =
              let uu____4007 =
                let uu____4012 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____4012  in
              let uu____4019 =
                let uu____4026 =
                  let uu____4031 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4031  in
                let uu____4036 =
                  let uu____4043 =
                    let uu____4048 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4048  in
                  [uu____4043]  in
                uu____4026 :: uu____4036  in
              uu____4007 :: uu____4019  in
            uu____3990 :: uu____4000  in
          uu____3973 :: uu____3983  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____3966
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4079 =
          let uu____4086 =
            let uu____4091 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4091  in
          let uu____4098 =
            let uu____4105 =
              let uu____4110 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____4110  in
            [uu____4105]  in
          uu____4086 :: uu____4098  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____4079
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____4144 =
          let uu____4151 =
            let uu____4156 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4156  in
          let uu____4163 =
            let uu____4170 =
              let uu____4175 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____4175  in
            let uu____4182 =
              let uu____4189 =
                let uu____4194 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____4194  in
              let uu____4199 =
                let uu____4206 =
                  let uu____4211 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4211  in
                let uu____4216 =
                  let uu____4223 =
                    let uu____4228 =
                      let uu____4229 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____4229 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4228  in
                  [uu____4223]  in
                uu____4206 :: uu____4216  in
              uu____4189 :: uu____4199  in
            uu____4170 :: uu____4182  in
          uu____4151 :: uu____4163  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____4144
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4300,(dcs,uu____4302)::(t1,uu____4304)::(bs,uu____4306)::
         (us,uu____4308)::(nm,uu____4310)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____4345 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____4345
          (fun nm1  ->
             let uu____4363 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____4363
               (fun us1  ->
                  let uu____4381 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____4381
                    (fun bs1  ->
                       let uu____4391 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____4391
                         (fun t2  ->
                            let uu____4401 =
                              let uu____4408 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____4408 cb
                                dcs
                               in
                            FStar_Util.bind_opt uu____4401
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4444,(t1,uu____4446)::(ty,uu____4448)::(univs1,uu____4450)::
         (fvar1,uu____4452)::(r,uu____4454)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____4489 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____4489
          (fun r1  ->
             let uu____4499 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1
                in
             FStar_Util.bind_opt uu____4499
               (fun fvar2  ->
                  let uu____4509 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____4509
                    (fun univs2  ->
                       let uu____4527 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____4527
                         (fun ty1  ->
                            let uu____4537 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____4537
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _0_44  ->
                                      FStar_Pervasives_Native.Some _0_44)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4551,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4566 ->
        ((let uu____4568 =
            let uu____4573 =
              let uu____4574 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4574
               in
            (FStar_Errors.Warning_NotEmbedded, uu____4573)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4568);
         FStar_Pervasives_Native.None)
     in
  let uu____4575 = mkFV FStar_Reflection_Data.fstar_refl_sigelt_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt_view unembed_sigelt_view
    uu____4575
  
let (e_exp : FStar_Reflection_Data.exp FStar_TypeChecker_NBETerm.embedding) =
  let rec embed_exp cb e =
    match e with
    | FStar_Reflection_Data.Unit  ->
        mkConstruct FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Var i ->
        let uu____4608 =
          let uu____4615 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____4615]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4608
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____4630 =
          let uu____4637 =
            let uu____4642 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4642  in
          let uu____4649 =
            let uu____4656 =
              let uu____4661 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4661  in
            [uu____4656]  in
          uu____4637 :: uu____4649  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4630
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4706,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4722,(i,uu____4724)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____4743 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____4743
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4755,(e2,uu____4757)::(e1,uu____4759)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____4782 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____4782
          (fun e11  ->
             let uu____4794 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____4794
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____4807 ->
        ((let uu____4809 =
            let uu____4814 =
              let uu____4815 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4815  in
            (FStar_Errors.Warning_NotEmbedded, uu____4814)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4809);
         FStar_Pervasives_Native.None)
     in
  let uu____4816 = mkFV FStar_Reflection_Data.fstar_refl_exp_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_exp unembed_exp uu____4816 
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_bv e_aqualv 
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding) = e_term 
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_attribute 