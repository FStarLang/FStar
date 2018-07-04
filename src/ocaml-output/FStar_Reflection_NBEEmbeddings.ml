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
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
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
      | uu____385 -> FStar_Pervasives_Native.None  in
    let uu____386 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____386
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
        let uu____433 =
          let uu____440 =
            let uu____445 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____445  in
          [uu____440]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____433
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____511)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____528 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____528
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____537 ->
        ((let uu____539 =
            let uu____544 =
              let uu____545 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____545  in
            (FStar_Errors.Warning_NotEmbedded, uu____544)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____539);
         FStar_Pervasives_Native.None)
     in
  let uu____546 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____546 
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
          FStar_Syntax_Syntax.ltyp = uu____602;
          FStar_Syntax_Syntax.rng = uu____603;_}
        ->
        let uu____606 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____606
    | uu____607 ->
        ((let uu____609 =
            let uu____614 =
              let uu____615 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____615  in
            (FStar_Errors.Warning_NotEmbedded, uu____614)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____609);
         FStar_Pervasives_Native.None)
     in
  let uu____616 = mkFV FStar_Reflection_Data.fstar_refl_fv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_fv unembed_fv uu____616 
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
          FStar_Syntax_Syntax.ltyp = uu____670;
          FStar_Syntax_Syntax.rng = uu____671;_}
        ->
        let uu____674 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____674
    | uu____675 ->
        ((let uu____677 =
            let uu____682 =
              let uu____683 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____683  in
            (FStar_Errors.Warning_NotEmbedded, uu____682)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____677);
         FStar_Pervasives_Native.None)
     in
  let uu____684 = mkFV FStar_Reflection_Data.fstar_refl_comp_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp unembed_comp uu____684 
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
          FStar_Syntax_Syntax.ltyp = uu____738;
          FStar_Syntax_Syntax.rng = uu____739;_}
        ->
        let uu____742 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____742
    | uu____743 ->
        ((let uu____745 =
            let uu____750 =
              let uu____751 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____751  in
            (FStar_Errors.Warning_NotEmbedded, uu____750)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____745);
         FStar_Pervasives_Native.None)
     in
  let uu____752 = mkFV FStar_Reflection_Data.fstar_refl_env_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_env unembed_env uu____752 
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
        let uu____793 =
          let uu____800 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____800]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____793
    | FStar_Reflection_Data.C_String s ->
        let uu____814 =
          let uu____821 =
            let uu____826 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string cb s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____826  in
          [uu____821]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____814
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____905)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____922 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____922
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____935)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____952 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb s
           in
        FStar_Util.bind_opt uu____952
          (fun s1  ->
             FStar_All.pipe_left
               (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
               (FStar_Reflection_Data.C_String s1))
    | uu____963 ->
        ((let uu____965 =
            let uu____970 =
              let uu____971 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____971  in
            (FStar_Errors.Warning_NotEmbedded, uu____970)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____965);
         FStar_Pervasives_Native.None)
     in
  let uu____972 = mkFV FStar_Reflection_Data.fstar_refl_vconst_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_const unembed_const uu____972 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____983  ->
    let embed_pattern cb p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1006 =
            let uu____1013 =
              let uu____1018 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1018  in
            [uu____1013]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____1006
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1037 =
            let uu____1044 =
              let uu____1049 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1049  in
            let uu____1054 =
              let uu____1061 =
                let uu____1066 =
                  let uu____1067 =
                    let uu____1072 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____1072  in
                  FStar_TypeChecker_NBETerm.embed uu____1067 cb ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____1066  in
              [uu____1061]  in
            uu____1044 :: uu____1054  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____1037
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1094 =
            let uu____1101 =
              let uu____1106 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1106  in
            [uu____1101]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____1094
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1120 =
            let uu____1127 =
              let uu____1132 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1132  in
            [uu____1127]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____1120
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1147 =
            let uu____1154 =
              let uu____1159 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1159  in
            let uu____1164 =
              let uu____1171 =
                let uu____1176 = FStar_TypeChecker_NBETerm.embed e_term cb t
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1176  in
              [uu____1171]  in
            uu____1154 :: uu____1164  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____1147
       in
    let unembed_pattern cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____1220)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____1237 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____1237
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____1250)::(f,uu____1252)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____1273 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____1273
            (fun f1  ->
               let uu____1283 =
                 let uu____1288 =
                   let uu____1293 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____1293  in
                 FStar_TypeChecker_NBETerm.unembed uu____1288 cb ps  in
               FStar_Util.bind_opt uu____1283
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1314)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1331 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1331
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1344)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1361 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1361
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____1374)::(bv,uu____1376)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1397 = FStar_TypeChecker_NBETerm.unembed e_bv cb bv  in
          FStar_Util.bind_opt uu____1397
            (fun bv1  ->
               let uu____1407 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____1407
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1418 ->
          ((let uu____1420 =
              let uu____1425 =
                let uu____1426 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1426
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1425)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1420);
           FStar_Pervasives_Native.None)
       in
    let uu____1427 = mkFV FStar_Reflection_Data.fstar_refl_pattern_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_pattern unembed_pattern uu____1427
  
let (e_pattern :
  FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding) =
  e_pattern' () 
let (e_branch :
  FStar_Reflection_Data.branch FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_pattern e_term 
let (e_argv : FStar_Reflection_Data.argv FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_tuple2 e_term e_aqualv 
let (e_branch_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1469 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1469
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1503 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1503 e_aqualv
  
let rec unlazy_as_t :
  'Auu____1512 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1512
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____1525;
            FStar_Syntax_Syntax.rng = uu____1526;_}
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1529 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view cb tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1579 =
            let uu____1586 =
              let uu____1591 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1591  in
            [uu____1586]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv []
            uu____1579
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1605 =
            let uu____1612 =
              let uu____1617 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1617  in
            [uu____1612]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1605
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1631 =
            let uu____1638 =
              let uu____1643 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1643  in
            [uu____1638]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1631
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1658 =
            let uu____1665 =
              let uu____1670 =
                let uu____1671 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1671 cb hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1670  in
            let uu____1678 =
              let uu____1685 =
                let uu____1690 =
                  let uu____1691 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1691 cb a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1690  in
              [uu____1685]  in
            uu____1665 :: uu____1678  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1658
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1720 =
            let uu____1727 =
              let uu____1732 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1732  in
            let uu____1737 =
              let uu____1744 =
                let uu____1749 =
                  let uu____1750 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1750 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1749  in
              [uu____1744]  in
            uu____1727 :: uu____1737  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1720
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1771 =
            let uu____1778 =
              let uu____1783 = FStar_TypeChecker_NBETerm.embed e_binder cb b
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1783  in
            let uu____1788 =
              let uu____1795 =
                let uu____1800 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1800  in
              [uu____1795]  in
            uu____1778 :: uu____1788  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1771
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1818 =
            let uu____1825 =
              let uu____1830 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit cb ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1830  in
            [uu____1825]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1818
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____1845 =
            let uu____1852 =
              let uu____1857 = FStar_TypeChecker_NBETerm.embed e_bv cb bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1857  in
            let uu____1862 =
              let uu____1869 =
                let uu____1874 =
                  let uu____1875 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1875 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1874  in
              [uu____1869]  in
            uu____1852 :: uu____1862  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1845
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1895 =
            let uu____1902 =
              let uu____1907 = FStar_TypeChecker_NBETerm.embed e_const cb c
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1907  in
            [uu____1902]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1895
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____1922 =
            let uu____1929 =
              let uu____1934 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int cb u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1934  in
            let uu____1939 =
              let uu____1946 =
                let uu____1951 =
                  mk_lazy (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1951  in
              [uu____1946]  in
            uu____1929 :: uu____1939  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____1922
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1972 =
            let uu____1979 =
              let uu____1984 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool cb r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1984  in
            let uu____1989 =
              let uu____1996 =
                let uu____2001 = FStar_TypeChecker_NBETerm.embed e_bv cb b
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2001  in
              let uu____2006 =
                let uu____2013 =
                  let uu____2018 =
                    let uu____2019 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____2019 cb t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2018  in
                let uu____2026 =
                  let uu____2033 =
                    let uu____2038 =
                      let uu____2039 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____2039 cb t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____2038  in
                  [uu____2033]  in
                uu____2013 :: uu____2026  in
              uu____1996 :: uu____2006  in
            uu____1979 :: uu____1989  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____1972
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____2072 =
            let uu____2079 =
              let uu____2084 =
                let uu____2085 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2085 cb t  in
              FStar_TypeChecker_NBETerm.as_arg uu____2084  in
            let uu____2092 =
              let uu____2099 =
                let uu____2104 =
                  let uu____2105 =
                    let uu____2114 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____2114  in
                  FStar_TypeChecker_NBETerm.embed uu____2105 cb brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____2104  in
              [uu____2099]  in
            uu____2079 :: uu____2092  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____2072
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____2154 =
            let uu____2161 =
              let uu____2166 =
                let uu____2167 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2167 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2166  in
            let uu____2174 =
              let uu____2181 =
                let uu____2186 =
                  let uu____2187 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____2187 cb t  in
                FStar_TypeChecker_NBETerm.as_arg uu____2186  in
              let uu____2194 =
                let uu____2201 =
                  let uu____2206 =
                    let uu____2207 =
                      let uu____2212 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2212  in
                    FStar_TypeChecker_NBETerm.embed uu____2207 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2206  in
                [uu____2201]  in
              uu____2181 :: uu____2194  in
            uu____2161 :: uu____2174  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2154
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2244 =
            let uu____2251 =
              let uu____2256 =
                let uu____2257 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____2257 cb e  in
              FStar_TypeChecker_NBETerm.as_arg uu____2256  in
            let uu____2264 =
              let uu____2271 =
                let uu____2276 = FStar_TypeChecker_NBETerm.embed e_comp cb c
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____2276  in
              let uu____2281 =
                let uu____2288 =
                  let uu____2293 =
                    let uu____2294 =
                      let uu____2299 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____2299  in
                    FStar_TypeChecker_NBETerm.embed uu____2294 cb tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____2293  in
                [uu____2288]  in
              uu____2271 :: uu____2281  in
            uu____2251 :: uu____2264  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____2244
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view cb t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2354,(b,uu____2356)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____2375 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2375
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2387,(b,uu____2389)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____2408 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2408
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2420,(f,uu____2422)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____2441 = FStar_TypeChecker_NBETerm.unembed e_fv cb f  in
          FStar_Util.bind_opt uu____2441
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2453,(r,uu____2455)::(l,uu____2457)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____2480 = FStar_TypeChecker_NBETerm.unembed e_term cb l  in
          FStar_Util.bind_opt uu____2480
            (fun l1  ->
               let uu____2490 = FStar_TypeChecker_NBETerm.unembed e_argv cb r
                  in
               FStar_Util.bind_opt uu____2490
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2502,(t1,uu____2504)::(b,uu____2506)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2529 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2529
            (fun b1  ->
               let uu____2539 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2539
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2551,(t1,uu____2553)::(b,uu____2555)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2578 = FStar_TypeChecker_NBETerm.unembed e_binder cb b
             in
          FStar_Util.bind_opt uu____2578
            (fun b1  ->
               let uu____2588 =
                 FStar_TypeChecker_NBETerm.unembed e_comp cb t1  in
               FStar_Util.bind_opt uu____2588
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2600,(u,uu____2602)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2621 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit cb u
             in
          FStar_Util.bind_opt uu____2621
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2633,(t1,uu____2635)::(b,uu____2637)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2660 = FStar_TypeChecker_NBETerm.unembed e_bv cb b  in
          FStar_Util.bind_opt uu____2660
            (fun b1  ->
               let uu____2670 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2670
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2682,(c,uu____2684)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2703 = FStar_TypeChecker_NBETerm.unembed e_const cb c  in
          FStar_Util.bind_opt uu____2703
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2715,(l,uu____2717)::(u,uu____2719)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2742 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              cb u
             in
          FStar_Util.bind_opt uu____2742
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2756,(t2,uu____2758)::(t1,uu____2760)::(b,uu____2762)::
           (r,uu____2764)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2795 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool cb r
             in
          FStar_Util.bind_opt uu____2795
            (fun r1  ->
               let uu____2805 = FStar_TypeChecker_NBETerm.unembed e_bv cb b
                  in
               FStar_Util.bind_opt uu____2805
                 (fun b1  ->
                    let uu____2815 =
                      FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                    FStar_Util.bind_opt uu____2815
                      (fun t11  ->
                         let uu____2825 =
                           FStar_TypeChecker_NBETerm.unembed e_term cb t2  in
                         FStar_Util.bind_opt uu____2825
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _0_34  ->
                                   FStar_Pervasives_Native.Some _0_34)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2837,(brs,uu____2839)::(t1,uu____2841)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2864 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
          FStar_Util.bind_opt uu____2864
            (fun t2  ->
               let uu____2874 =
                 let uu____2879 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2879 cb brs  in
               FStar_Util.bind_opt uu____2874
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2901,(tacopt,uu____2903)::(t1,uu____2905)::(e,uu____2907)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2934 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____2934
            (fun e1  ->
               let uu____2944 =
                 FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
               FStar_Util.bind_opt uu____2944
                 (fun t2  ->
                    let uu____2954 =
                      let uu____2959 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2959 cb tacopt
                       in
                    FStar_Util.bind_opt uu____2954
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2981,(tacopt,uu____2983)::(c,uu____2985)::(e,uu____2987)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____3014 = FStar_TypeChecker_NBETerm.unembed e_term cb e  in
          FStar_Util.bind_opt uu____3014
            (fun e1  ->
               let uu____3024 = FStar_TypeChecker_NBETerm.unembed e_comp cb c
                  in
               FStar_Util.bind_opt uu____3024
                 (fun c1  ->
                    let uu____3034 =
                      let uu____3039 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____3039 cb tacopt
                       in
                    FStar_Util.bind_opt uu____3034
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____3061,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
            FStar_Reflection_Data.Tv_Unknown
      | uu____3078 ->
          ((let uu____3080 =
              let uu____3085 =
                let uu____3086 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____3086
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3085)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____3080);
           FStar_Pervasives_Native.None)
       in
    let uu____3087 = mkFV FStar_Reflection_Data.fstar_refl_term_view_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_term_view unembed_term_view
      uu____3087
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view cb bvv =
    let uu____3125 =
      let uu____3132 =
        let uu____3137 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            cb bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____3137  in
      let uu____3142 =
        let uu____3149 =
          let uu____3154 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              cb bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____3154  in
        let uu____3159 =
          let uu____3166 =
            let uu____3171 =
              FStar_TypeChecker_NBETerm.embed e_term cb
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3171  in
          [uu____3166]  in
        uu____3149 :: uu____3159  in
      uu____3132 :: uu____3142  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____3125
     in
  let unembed_bv_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3218,(s,uu____3220)::(idx,uu____3222)::(nm,uu____3224)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____3251 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string cb nm
           in
        FStar_Util.bind_opt uu____3251
          (fun nm1  ->
             let uu____3261 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int cb idx
                in
             FStar_Util.bind_opt uu____3261
               (fun idx1  ->
                  let uu____3271 =
                    FStar_TypeChecker_NBETerm.unembed e_term cb s  in
                  FStar_Util.bind_opt uu____3271
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____3282 ->
        ((let uu____3284 =
            let uu____3289 =
              let uu____3290 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____3290  in
            (FStar_Errors.Warning_NotEmbedded, uu____3289)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3284);
         FStar_Pervasives_Native.None)
     in
  let uu____3291 = mkFV FStar_Reflection_Data.fstar_refl_bv_view_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_bv_view unembed_bv_view uu____3291 
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____3325 =
          let uu____3332 =
            let uu____3337 = FStar_TypeChecker_NBETerm.embed e_term cb t  in
            FStar_TypeChecker_NBETerm.as_arg uu____3337  in
          let uu____3342 =
            let uu____3349 =
              let uu____3354 =
                let uu____3355 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____3355 cb md  in
              FStar_TypeChecker_NBETerm.as_arg uu____3354  in
            [uu____3349]  in
          uu____3332 :: uu____3342  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____3325
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3383 =
          let uu____3390 =
            let uu____3395 = FStar_TypeChecker_NBETerm.embed e_term cb pre
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3395  in
          let uu____3400 =
            let uu____3407 =
              let uu____3412 =
                FStar_TypeChecker_NBETerm.embed e_term cb post1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3412  in
            [uu____3407]  in
          uu____3390 :: uu____3400  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____3383
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3459,(md,uu____3461)::(t1,uu____3463)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____3486 = FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
        FStar_Util.bind_opt uu____3486
          (fun t2  ->
             let uu____3496 =
               let uu____3501 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____3501 cb md  in
             FStar_Util.bind_opt uu____3496
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3523,(post,uu____3525)::(pre,uu____3527)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____3550 = FStar_TypeChecker_NBETerm.unembed e_term cb pre  in
        FStar_Util.bind_opt uu____3550
          (fun pre1  ->
             let uu____3560 =
               FStar_TypeChecker_NBETerm.unembed e_term cb post  in
             FStar_Util.bind_opt uu____3560
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3572,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
          FStar_Reflection_Data.C_Unknown
    | uu____3589 ->
        ((let uu____3591 =
            let uu____3596 =
              let uu____3597 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____3597
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3596)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3591);
         FStar_Pervasives_Native.None)
     in
  let uu____3598 = mkFV FStar_Reflection_Data.fstar_refl_comp_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp_view unembed_comp_view
    uu____3598
  
let (e_order : FStar_Order.order FStar_TypeChecker_NBETerm.embedding) =
  let embed_order cb o =
    match o with
    | FStar_Order.Lt  -> mkConstruct FStar_Reflection_Data.ord_Lt_fv [] []
    | FStar_Order.Eq  -> mkConstruct FStar_Reflection_Data.ord_Eq_fv [] []
    | FStar_Order.Gt  -> mkConstruct FStar_Reflection_Data.ord_Gt_fv [] []
     in
  let unembed_order cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3664,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3680,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3696,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____3711 ->
        ((let uu____3713 =
            let uu____3718 =
              let uu____3719 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____3719  in
            (FStar_Errors.Warning_NotEmbedded, uu____3718)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3713);
         FStar_Pervasives_Native.None)
     in
  let uu____3720 =
    let uu____3721 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____3721 [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_order unembed_order uu____3720 
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
          FStar_Syntax_Syntax.ltyp = uu____3775;
          FStar_Syntax_Syntax.rng = uu____3776;_}
        ->
        let uu____3779 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____3779
    | uu____3780 ->
        ((let uu____3782 =
            let uu____3787 =
              let uu____3788 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3788  in
            (FStar_Errors.Warning_NotEmbedded, uu____3787)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3782);
         FStar_Pervasives_Native.None)
     in
  let uu____3789 = mkFV FStar_Reflection_Data.fstar_refl_sigelt_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt unembed_sigelt uu____3789 
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string
     in
  let embed_ident cb i =
    let uu____3826 =
      let uu____3831 = FStar_Ident.range_of_id i  in
      let uu____3832 = FStar_Ident.text_of_id i  in (uu____3831, uu____3832)
       in
    FStar_TypeChecker_NBETerm.embed repr cb uu____3826  in
  let unembed_ident cb t =
    let uu____3866 = FStar_TypeChecker_NBETerm.unembed repr cb t  in
    match uu____3866 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____3889 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____3889
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____3894 =
    let uu____3895 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____3896 =
      let uu____3903 =
        let uu____3908 =
          let uu____3909 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          mkFV uu____3909 [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____3908  in
      let uu____3914 =
        let uu____3921 =
          let uu____3926 =
            let uu____3927 =
              FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            mkFV uu____3927 [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____3926  in
        [uu____3921]  in
      uu____3903 :: uu____3914  in
    mkFV uu____3895 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____3896
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3894 
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
        let uu____3986 =
          let uu____3993 =
            let uu____3998 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool cb r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3998  in
          let uu____4003 =
            let uu____4010 =
              let uu____4015 = FStar_TypeChecker_NBETerm.embed e_fv cb fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____4015  in
            let uu____4020 =
              let uu____4027 =
                let uu____4032 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____4032  in
              let uu____4039 =
                let uu____4046 =
                  let uu____4051 =
                    FStar_TypeChecker_NBETerm.embed e_term cb ty  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4051  in
                let uu____4056 =
                  let uu____4063 =
                    let uu____4068 =
                      FStar_TypeChecker_NBETerm.embed e_term cb t  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4068  in
                  [uu____4063]  in
                uu____4046 :: uu____4056  in
              uu____4027 :: uu____4039  in
            uu____4010 :: uu____4020  in
          uu____3993 :: uu____4003  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____3986
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4099 =
          let uu____4106 =
            let uu____4111 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4111  in
          let uu____4118 =
            let uu____4125 =
              let uu____4130 = FStar_TypeChecker_NBETerm.embed e_term cb ty
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____4130  in
            [uu____4125]  in
          uu____4106 :: uu____4118  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____4099
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____4164 =
          let uu____4171 =
            let uu____4176 =
              FStar_TypeChecker_NBETerm.embed e_string_list cb nm  in
            FStar_TypeChecker_NBETerm.as_arg uu____4176  in
          let uu____4183 =
            let uu____4190 =
              let uu____4195 =
                FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____4195  in
            let uu____4202 =
              let uu____4209 =
                let uu____4214 =
                  FStar_TypeChecker_NBETerm.embed e_binders cb bs  in
                FStar_TypeChecker_NBETerm.as_arg uu____4214  in
              let uu____4219 =
                let uu____4226 =
                  let uu____4231 =
                    FStar_TypeChecker_NBETerm.embed e_term cb t  in
                  FStar_TypeChecker_NBETerm.as_arg uu____4231  in
                let uu____4236 =
                  let uu____4243 =
                    let uu____4248 =
                      let uu____4249 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____4249 cb dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____4248  in
                  [uu____4243]  in
                uu____4226 :: uu____4236  in
              uu____4209 :: uu____4219  in
            uu____4190 :: uu____4202  in
          uu____4171 :: uu____4183  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____4164
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4320,(dcs,uu____4322)::(t1,uu____4324)::(bs,uu____4326)::
         (us,uu____4328)::(nm,uu____4330)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____4365 =
          FStar_TypeChecker_NBETerm.unembed e_string_list cb nm  in
        FStar_Util.bind_opt uu____4365
          (fun nm1  ->
             let uu____4383 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names cb us  in
             FStar_Util.bind_opt uu____4383
               (fun us1  ->
                  let uu____4401 =
                    FStar_TypeChecker_NBETerm.unembed e_binders cb bs  in
                  FStar_Util.bind_opt uu____4401
                    (fun bs1  ->
                       let uu____4411 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb t1  in
                       FStar_Util.bind_opt uu____4411
                         (fun t2  ->
                            let uu____4421 =
                              let uu____4428 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____4428 cb
                                dcs
                               in
                            FStar_Util.bind_opt uu____4421
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4464,(t1,uu____4466)::(ty,uu____4468)::(univs1,uu____4470)::
         (fvar1,uu____4472)::(r,uu____4474)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____4509 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            cb r
           in
        FStar_Util.bind_opt uu____4509
          (fun r1  ->
             let uu____4519 = FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1
                in
             FStar_Util.bind_opt uu____4519
               (fun fvar2  ->
                  let uu____4529 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1
                     in
                  FStar_Util.bind_opt uu____4529
                    (fun univs2  ->
                       let uu____4547 =
                         FStar_TypeChecker_NBETerm.unembed e_term cb ty  in
                       FStar_Util.bind_opt uu____4547
                         (fun ty1  ->
                            let uu____4557 =
                              FStar_TypeChecker_NBETerm.unembed e_term cb t1
                               in
                            FStar_Util.bind_opt uu____4557
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _0_44  ->
                                      FStar_Pervasives_Native.Some _0_44)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4571,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____4586 ->
        ((let uu____4588 =
            let uu____4593 =
              let uu____4594 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4594
               in
            (FStar_Errors.Warning_NotEmbedded, uu____4593)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4588);
         FStar_Pervasives_Native.None)
     in
  let uu____4595 = mkFV FStar_Reflection_Data.fstar_refl_sigelt_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt_view unembed_sigelt_view
    uu____4595
  
let (e_exp : FStar_Reflection_Data.exp FStar_TypeChecker_NBETerm.embedding) =
  let rec embed_exp cb e =
    match e with
    | FStar_Reflection_Data.Unit  ->
        mkConstruct FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Var i ->
        let uu____4628 =
          let uu____4635 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____4635]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____4628
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____4650 =
          let uu____4657 =
            let uu____4662 = embed_exp cb e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____4662  in
          let uu____4669 =
            let uu____4676 =
              let uu____4681 = embed_exp cb e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____4681  in
            [uu____4676]  in
          uu____4657 :: uu____4669  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____4650
     in
  let rec unembed_exp cb t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4726,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____4742,(i,uu____4744)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____4763 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
            cb i
           in
        FStar_Util.bind_opt uu____4763
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____4775,(e2,uu____4777)::(e1,uu____4779)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____4802 = unembed_exp cb e1  in
        FStar_Util.bind_opt uu____4802
          (fun e11  ->
             let uu____4814 = unembed_exp cb e2  in
             FStar_Util.bind_opt uu____4814
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____4827 ->
        ((let uu____4829 =
            let uu____4834 =
              let uu____4835 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____4835  in
            (FStar_Errors.Warning_NotEmbedded, uu____4834)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4829);
         FStar_Pervasives_Native.None)
     in
  let uu____4836 = mkFV FStar_Reflection_Data.fstar_refl_exp_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_exp unembed_exp uu____4836 
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_bv e_aqualv 
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding) = e_term 
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_attribute 