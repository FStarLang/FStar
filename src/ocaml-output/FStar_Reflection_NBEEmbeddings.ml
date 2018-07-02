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
  let embed_bv bv =
    mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv
     in
  let unembed_bv t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____120;
          FStar_Syntax_Syntax.rng = uu____121;_}
        ->
        let uu____124 = FStar_Dyn.undyn b  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____124
    | uu____127 ->
        ((let uu____129 =
            let uu____134 =
              let uu____135 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____135  in
            (FStar_Errors.Warning_NotEmbedded, uu____134)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____129);
         FStar_Pervasives_Native.None)
     in
  let uu____136 = mkFV FStar_Reflection_Data.fstar_refl_bv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_bv unembed_bv uu____136 
let (e_binder :
  FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding) =
  let embed_binder b =
    mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder
     in
  let unembed_binder t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____160;
          FStar_Syntax_Syntax.rng = uu____161;_}
        ->
        let uu____164 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____164
    | uu____165 ->
        ((let uu____167 =
            let uu____172 =
              let uu____173 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____173  in
            (FStar_Errors.Warning_NotEmbedded, uu____172)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____167);
         FStar_Pervasives_Native.None)
     in
  let uu____174 = mkFV FStar_Reflection_Data.fstar_refl_binder_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_binder unembed_binder uu____174 
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
          let uu____224 = f x  in
          FStar_Util.bind_opt uu____224
            (fun x1  ->
               let uu____232 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____232
                 (fun xs1  -> FStar_Pervasives_Native.Some (x1 :: xs1)))
  
let (e_term_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term t =
      let qi =
        {
          FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
          FStar_Syntax_Syntax.antiquotes = aq
        }  in
      FStar_TypeChecker_NBETerm.Quote (t, qi)  in
    let rec unembed_term t =
      match t with
      | FStar_TypeChecker_NBETerm.Quote (tm,qi) ->
          FStar_Pervasives_Native.Some tm
      | uu____295 -> FStar_Pervasives_Native.None  in
    let uu____296 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____296
    }
  
let (e_term : FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding) =
  e_term_aq [] 
let (e_aqualv :
  FStar_Reflection_Data.aqualv FStar_TypeChecker_NBETerm.embedding) =
  let embed_aqualv q =
    match q with
    | FStar_Reflection_Data.Q_Explicit  ->
        mkConstruct
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Q_Implicit  ->
        mkConstruct
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Q_Meta t ->
        let uu____328 =
          let uu____335 =
            let uu____340 = FStar_TypeChecker_NBETerm.embed e_term t  in
            FStar_TypeChecker_NBETerm.as_arg uu____340  in
          [uu____335]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____328
     in
  let unembed_aqualv t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
    | FStar_TypeChecker_NBETerm.Construct (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____387)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____404 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
        FStar_Util.bind_opt uu____404
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____409 ->
        ((let uu____411 =
            let uu____416 =
              let uu____417 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____417  in
            (FStar_Errors.Warning_NotEmbedded, uu____416)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____411);
         FStar_Pervasives_Native.None)
     in
  let uu____418 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____418 
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_list e_binder 
let (e_fv : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding) =
  let embed_fv fv =
    mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar
     in
  let unembed_fv t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____444;
          FStar_Syntax_Syntax.rng = uu____445;_}
        ->
        let uu____448 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____448
    | uu____449 ->
        ((let uu____451 =
            let uu____456 =
              let uu____457 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____457  in
            (FStar_Errors.Warning_NotEmbedded, uu____456)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____451);
         FStar_Pervasives_Native.None)
     in
  let uu____458 = mkFV FStar_Reflection_Data.fstar_refl_fv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_fv unembed_fv uu____458 
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp c =
    mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp
     in
  let unembed_comp t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____482;
          FStar_Syntax_Syntax.rng = uu____483;_}
        ->
        let uu____486 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____486
    | uu____487 ->
        ((let uu____489 =
            let uu____494 =
              let uu____495 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____495  in
            (FStar_Errors.Warning_NotEmbedded, uu____494)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____489);
         FStar_Pervasives_Native.None)
     in
  let uu____496 = mkFV FStar_Reflection_Data.fstar_refl_comp_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp unembed_comp uu____496 
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env e =
    mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env
     in
  let unembed_env t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____520;
          FStar_Syntax_Syntax.rng = uu____521;_}
        ->
        let uu____524 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____524
    | uu____525 ->
        ((let uu____527 =
            let uu____532 =
              let uu____533 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____533  in
            (FStar_Errors.Warning_NotEmbedded, uu____532)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____527);
         FStar_Pervasives_Native.None)
     in
  let uu____534 = mkFV FStar_Reflection_Data.fstar_refl_env_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_env unembed_env uu____534 
let (e_const :
  FStar_Reflection_Data.vconst FStar_TypeChecker_NBETerm.embedding) =
  let embed_const c =
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
        let uu____560 =
          let uu____567 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____567]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____560
    | FStar_Reflection_Data.C_String s ->
        let uu____581 =
          let uu____588 =
            let uu____593 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____593  in
          [uu____588]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____581
     in
  let unembed_const t =
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____653)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____670 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int i
           in
        FStar_Util.bind_opt uu____670
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____679)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____696 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string s
           in
        FStar_Util.bind_opt uu____696
          (fun s1  ->
             FStar_All.pipe_left
               (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
               (FStar_Reflection_Data.C_String s1))
    | uu____703 ->
        ((let uu____705 =
            let uu____710 =
              let uu____711 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____711  in
            (FStar_Errors.Warning_NotEmbedded, uu____710)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____705);
         FStar_Pervasives_Native.None)
     in
  let uu____712 = mkFV FStar_Reflection_Data.fstar_refl_vconst_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_const unembed_const uu____712 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____723  ->
    let rec embed_pattern p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____731 =
            let uu____738 =
              let uu____743 = FStar_TypeChecker_NBETerm.embed e_const c  in
              FStar_TypeChecker_NBETerm.as_arg uu____743  in
            [uu____738]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____731
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____758 =
            let uu____765 =
              let uu____770 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____770  in
            let uu____771 =
              let uu____778 =
                let uu____783 =
                  let uu____784 =
                    let uu____789 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____789  in
                  FStar_TypeChecker_NBETerm.embed uu____784 ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____783  in
              [uu____778]  in
            uu____765 :: uu____771  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____758
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____807 =
            let uu____814 =
              let uu____819 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____819  in
            [uu____814]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____807
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____829 =
            let uu____836 =
              let uu____841 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____841  in
            [uu____836]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____829
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____852 =
            let uu____859 =
              let uu____864 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____864  in
            let uu____865 =
              let uu____872 =
                let uu____877 = FStar_TypeChecker_NBETerm.embed e_term t  in
                FStar_TypeChecker_NBETerm.as_arg uu____877  in
              [uu____872]  in
            uu____859 :: uu____865  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____852
       in
    let rec unembed_pattern t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____902)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____919 = FStar_TypeChecker_NBETerm.unembed e_const c  in
          FStar_Util.bind_opt uu____919
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____928)::(f,uu____930)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____951 = FStar_TypeChecker_NBETerm.unembed e_fv f  in
          FStar_Util.bind_opt uu____951
            (fun f1  ->
               let uu____957 =
                 let uu____962 =
                   let uu____967 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____967  in
                 FStar_TypeChecker_NBETerm.unembed uu____962 ps  in
               FStar_Util.bind_opt uu____957
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____984)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____1001 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____1001
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____1010)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1027 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____1027
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____1036)::(bv,uu____1038)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1059 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____1059
            (fun bv1  ->
               let uu____1065 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____1065
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1072 ->
          ((let uu____1074 =
              let uu____1079 =
                let uu____1080 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1080
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1079)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1074);
           FStar_Pervasives_Native.None)
       in
    let uu____1081 = mkFV FStar_Reflection_Data.fstar_refl_pattern_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_pattern unembed_pattern uu____1081
  
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
    let uu____1123 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1123
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1157 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1157 e_aqualv
  
let rec unlazy_as_t :
  'Auu____1166 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1166
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____1179;
            FStar_Syntax_Syntax.rng = uu____1180;_}
          when FStar_Syntax_Util.eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____1183 -> failwith "Not a Lazy of the expected kind (NBE)"
  
let (e_term_view_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term_view tv =
      match tv with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1218 =
            let uu____1225 =
              let uu____1230 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1230  in
            [uu____1225]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1218
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1240 =
            let uu____1247 =
              let uu____1252 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1252  in
            [uu____1247]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1240
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1262 =
            let uu____1269 =
              let uu____1274 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1274  in
            [uu____1269]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1262
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1285 =
            let uu____1292 =
              let uu____1297 =
                let uu____1298 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1298 hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1297  in
            let uu____1301 =
              let uu____1308 =
                let uu____1313 =
                  let uu____1314 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1314 a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1313  in
              [uu____1308]  in
            uu____1292 :: uu____1301  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1285
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1339 =
            let uu____1346 =
              let uu____1351 = FStar_TypeChecker_NBETerm.embed e_binder b  in
              FStar_TypeChecker_NBETerm.as_arg uu____1351  in
            let uu____1352 =
              let uu____1359 =
                let uu____1364 =
                  let uu____1365 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1365 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1364  in
              [uu____1359]  in
            uu____1346 :: uu____1352  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1339
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1382 =
            let uu____1389 =
              let uu____1394 = FStar_TypeChecker_NBETerm.embed e_binder b  in
              FStar_TypeChecker_NBETerm.as_arg uu____1394  in
            let uu____1395 =
              let uu____1402 =
                let uu____1407 = FStar_TypeChecker_NBETerm.embed e_comp c  in
                FStar_TypeChecker_NBETerm.as_arg uu____1407  in
              [uu____1402]  in
            uu____1389 :: uu____1395  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1382
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1421 =
            let uu____1428 =
              let uu____1433 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1433  in
            [uu____1428]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1421
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____1444 =
            let uu____1451 =
              let uu____1456 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1456  in
            let uu____1457 =
              let uu____1464 =
                let uu____1469 =
                  let uu____1470 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1470 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1469  in
              [uu____1464]  in
            uu____1451 :: uu____1457  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1444
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1486 =
            let uu____1493 =
              let uu____1498 = FStar_TypeChecker_NBETerm.embed e_const c  in
              FStar_TypeChecker_NBETerm.as_arg uu____1498  in
            [uu____1493]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1486
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____1509 =
            let uu____1516 =
              let uu____1521 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1521  in
            let uu____1522 =
              let uu____1529 =
                let uu____1534 =
                  mk_lazy (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1534  in
              [uu____1529]  in
            uu____1516 :: uu____1522  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____1509
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1555 =
            let uu____1562 =
              let uu____1567 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1567  in
            let uu____1568 =
              let uu____1575 =
                let uu____1580 = FStar_TypeChecker_NBETerm.embed e_bv b  in
                FStar_TypeChecker_NBETerm.as_arg uu____1580  in
              let uu____1581 =
                let uu____1588 =
                  let uu____1593 =
                    let uu____1594 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____1594 t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1593  in
                let uu____1597 =
                  let uu____1604 =
                    let uu____1609 =
                      let uu____1610 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____1610 t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____1609  in
                  [uu____1604]  in
                uu____1588 :: uu____1597  in
              uu____1575 :: uu____1581  in
            uu____1562 :: uu____1568  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____1555
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____1639 =
            let uu____1646 =
              let uu____1651 =
                let uu____1652 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1652 t  in
              FStar_TypeChecker_NBETerm.as_arg uu____1651  in
            let uu____1655 =
              let uu____1662 =
                let uu____1667 =
                  let uu____1668 =
                    let uu____1677 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____1677  in
                  FStar_TypeChecker_NBETerm.embed uu____1668 brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____1667  in
              [uu____1662]  in
            uu____1646 :: uu____1655  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____1639
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____1713 =
            let uu____1720 =
              let uu____1725 =
                let uu____1726 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1726 e  in
              FStar_TypeChecker_NBETerm.as_arg uu____1725  in
            let uu____1729 =
              let uu____1736 =
                let uu____1741 =
                  let uu____1742 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1742 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1741  in
              let uu____1745 =
                let uu____1752 =
                  let uu____1757 =
                    let uu____1758 =
                      let uu____1763 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____1763  in
                    FStar_TypeChecker_NBETerm.embed uu____1758 tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1757  in
                [uu____1752]  in
              uu____1736 :: uu____1745  in
            uu____1720 :: uu____1729  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____1713
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____1791 =
            let uu____1798 =
              let uu____1803 =
                let uu____1804 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1804 e  in
              FStar_TypeChecker_NBETerm.as_arg uu____1803  in
            let uu____1807 =
              let uu____1814 =
                let uu____1819 = FStar_TypeChecker_NBETerm.embed e_comp c  in
                FStar_TypeChecker_NBETerm.as_arg uu____1819  in
              let uu____1820 =
                let uu____1827 =
                  let uu____1832 =
                    let uu____1833 =
                      let uu____1838 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____1838  in
                    FStar_TypeChecker_NBETerm.embed uu____1833 tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1832  in
                [uu____1827]  in
              uu____1814 :: uu____1820  in
            uu____1798 :: uu____1807  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____1791
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1874,(b,uu____1876)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____1895 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1895
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1903,(b,uu____1905)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____1924 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1924
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1932,(f,uu____1934)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____1953 = FStar_TypeChecker_NBETerm.unembed e_fv f  in
          FStar_Util.bind_opt uu____1953
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1961,(r,uu____1963)::(l,uu____1965)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____1988 = FStar_TypeChecker_NBETerm.unembed e_term l  in
          FStar_Util.bind_opt uu____1988
            (fun l1  ->
               let uu____1994 = FStar_TypeChecker_NBETerm.unembed e_argv r
                  in
               FStar_Util.bind_opt uu____1994
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2002,(t1,uu____2004)::(b,uu____2006)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2029 = FStar_TypeChecker_NBETerm.unembed e_binder b  in
          FStar_Util.bind_opt uu____2029
            (fun b1  ->
               let uu____2035 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____2035
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2043,(t1,uu____2045)::(b,uu____2047)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2070 = FStar_TypeChecker_NBETerm.unembed e_binder b  in
          FStar_Util.bind_opt uu____2070
            (fun b1  ->
               let uu____2076 = FStar_TypeChecker_NBETerm.unembed e_comp t1
                  in
               FStar_Util.bind_opt uu____2076
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2084,(u,uu____2086)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2105 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit u
             in
          FStar_Util.bind_opt uu____2105
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2113,(t1,uu____2115)::(b,uu____2117)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2140 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____2140
            (fun b1  ->
               let uu____2146 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____2146
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2154,(c,uu____2156)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2175 = FStar_TypeChecker_NBETerm.unembed e_const c  in
          FStar_Util.bind_opt uu____2175
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2183,(l,uu____2185)::(u,uu____2187)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2210 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              u
             in
          FStar_Util.bind_opt uu____2210
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2220,(t2,uu____2222)::(t1,uu____2224)::(b,uu____2226)::
           (r,uu____2228)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2259 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool r
             in
          FStar_Util.bind_opt uu____2259
            (fun r1  ->
               let uu____2265 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
               FStar_Util.bind_opt uu____2265
                 (fun b1  ->
                    let uu____2271 =
                      FStar_TypeChecker_NBETerm.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2271
                      (fun t11  ->
                         let uu____2277 =
                           FStar_TypeChecker_NBETerm.unembed e_term t2  in
                         FStar_Util.bind_opt uu____2277
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _0_34  ->
                                   FStar_Pervasives_Native.Some _0_34)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2285,(brs,uu____2287)::(t1,uu____2289)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2312 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
          FStar_Util.bind_opt uu____2312
            (fun t2  ->
               let uu____2318 =
                 let uu____2323 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2323 brs  in
               FStar_Util.bind_opt uu____2318
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2341,(tacopt,uu____2343)::(t1,uu____2345)::(e,uu____2347)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2374 = FStar_TypeChecker_NBETerm.unembed e_term e  in
          FStar_Util.bind_opt uu____2374
            (fun e1  ->
               let uu____2380 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____2380
                 (fun t2  ->
                    let uu____2386 =
                      let uu____2391 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2391 tacopt  in
                    FStar_Util.bind_opt uu____2386
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2409,(tacopt,uu____2411)::(c,uu____2413)::(e,uu____2415)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____2442 = FStar_TypeChecker_NBETerm.unembed e_term e  in
          FStar_Util.bind_opt uu____2442
            (fun e1  ->
               let uu____2448 = FStar_TypeChecker_NBETerm.unembed e_comp c
                  in
               FStar_Util.bind_opt uu____2448
                 (fun c1  ->
                    let uu____2454 =
                      let uu____2459 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2459 tacopt  in
                    FStar_Util.bind_opt uu____2454
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____2477,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
            FStar_Reflection_Data.Tv_Unknown
      | uu____2494 ->
          ((let uu____2496 =
              let uu____2501 =
                let uu____2502 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____2502
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2501)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2496);
           FStar_Pervasives_Native.None)
       in
    let uu____2503 = mkFV FStar_Reflection_Data.fstar_refl_term_view_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_term_view unembed_term_view
      uu____2503
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view bvv =
    let uu____2526 =
      let uu____2533 =
        let uu____2538 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____2538  in
      let uu____2539 =
        let uu____2546 =
          let uu____2551 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____2551  in
        let uu____2552 =
          let uu____2559 =
            let uu____2564 =
              FStar_TypeChecker_NBETerm.embed e_term
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2564  in
          [uu____2559]  in
        uu____2546 :: uu____2552  in
      uu____2533 :: uu____2539  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____2526
     in
  let unembed_bv_view t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____2592,(s,uu____2594)::(idx,uu____2596)::(nm,uu____2598)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____2625 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string nm
           in
        FStar_Util.bind_opt uu____2625
          (fun nm1  ->
             let uu____2631 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int idx
                in
             FStar_Util.bind_opt uu____2631
               (fun idx1  ->
                  let uu____2637 = FStar_TypeChecker_NBETerm.unembed e_term s
                     in
                  FStar_Util.bind_opt uu____2637
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____2644 ->
        ((let uu____2646 =
            let uu____2651 =
              let uu____2652 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____2652  in
            (FStar_Errors.Warning_NotEmbedded, uu____2651)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2646);
         FStar_Pervasives_Native.None)
     in
  let uu____2653 = mkFV FStar_Reflection_Data.fstar_refl_bv_view_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_bv_view unembed_bv_view uu____2653 
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____2672 =
          let uu____2679 =
            let uu____2684 = FStar_TypeChecker_NBETerm.embed e_term t  in
            FStar_TypeChecker_NBETerm.as_arg uu____2684  in
          let uu____2685 =
            let uu____2692 =
              let uu____2697 =
                let uu____2698 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____2698 md  in
              FStar_TypeChecker_NBETerm.as_arg uu____2697  in
            [uu____2692]  in
          uu____2679 :: uu____2685  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____2672
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____2722 =
          let uu____2729 =
            let uu____2734 = FStar_TypeChecker_NBETerm.embed e_term pre  in
            FStar_TypeChecker_NBETerm.as_arg uu____2734  in
          let uu____2735 =
            let uu____2742 =
              let uu____2747 = FStar_TypeChecker_NBETerm.embed e_term post1
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2747  in
            [uu____2742]  in
          uu____2729 :: uu____2735  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____2722
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____2775,(md,uu____2777)::(t1,uu____2779)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____2802 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
        FStar_Util.bind_opt uu____2802
          (fun t2  ->
             let uu____2808 =
               let uu____2813 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____2813 md  in
             FStar_Util.bind_opt uu____2808
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____2831,(post,uu____2833)::(pre,uu____2835)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____2858 = FStar_TypeChecker_NBETerm.unembed e_term pre  in
        FStar_Util.bind_opt uu____2858
          (fun pre1  ->
             let uu____2864 = FStar_TypeChecker_NBETerm.unembed e_term post
                in
             FStar_Util.bind_opt uu____2864
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2872,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
          FStar_Reflection_Data.C_Unknown
    | uu____2889 ->
        ((let uu____2891 =
            let uu____2896 =
              let uu____2897 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____2897
               in
            (FStar_Errors.Warning_NotEmbedded, uu____2896)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2891);
         FStar_Pervasives_Native.None)
     in
  let uu____2898 = mkFV FStar_Reflection_Data.fstar_refl_comp_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp_view unembed_comp_view
    uu____2898
  
let (e_order : FStar_Order.order FStar_TypeChecker_NBETerm.embedding) =
  let embed_order o =
    match o with
    | FStar_Order.Lt  -> mkConstruct FStar_Reflection_Data.ord_Lt_fv [] []
    | FStar_Order.Eq  -> mkConstruct FStar_Reflection_Data.ord_Eq_fv [] []
    | FStar_Order.Gt  -> mkConstruct FStar_Reflection_Data.ord_Gt_fv [] []
     in
  let unembed_order t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2934,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2950,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2966,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____2981 ->
        ((let uu____2983 =
            let uu____2988 =
              let uu____2989 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____2989  in
            (FStar_Errors.Warning_NotEmbedded, uu____2988)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2983);
         FStar_Pervasives_Native.None)
     in
  let uu____2990 =
    let uu____2991 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____2991 [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_order unembed_order uu____2990 
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt se =
    mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt
     in
  let unembed_sigelt t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____3015;
          FStar_Syntax_Syntax.rng = uu____3016;_}
        ->
        let uu____3019 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____3019
    | uu____3020 ->
        ((let uu____3022 =
            let uu____3027 =
              let uu____3028 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3028  in
            (FStar_Errors.Warning_NotEmbedded, uu____3027)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3022);
         FStar_Pervasives_Native.None)
     in
  let uu____3029 = mkFV FStar_Reflection_Data.fstar_refl_sigelt_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt unembed_sigelt uu____3029 
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string
     in
  let embed_ident i =
    let uu____3051 =
      let uu____3056 = FStar_Ident.range_of_id i  in
      let uu____3057 = FStar_Ident.text_of_id i  in (uu____3056, uu____3057)
       in
    FStar_TypeChecker_NBETerm.embed repr uu____3051  in
  let unembed_ident t =
    let uu____3072 = FStar_TypeChecker_NBETerm.unembed repr t  in
    match uu____3072 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____3091 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____3091
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____3096 =
    let uu____3097 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____3098 =
      let uu____3105 =
        let uu____3110 =
          let uu____3111 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          mkFV uu____3111 [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____3110  in
      let uu____3116 =
        let uu____3123 =
          let uu____3128 =
            let uu____3129 =
              FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            mkFV uu____3129 [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____3128  in
        [uu____3123]  in
      uu____3105 :: uu____3116  in
    mkFV uu____3097 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____3098
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3096 
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
  let embed_sigelt_view sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,univs1,ty,t) ->
        let uu____3173 =
          let uu____3180 =
            let uu____3185 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3185  in
          let uu____3186 =
            let uu____3193 =
              let uu____3198 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3198  in
            let uu____3199 =
              let uu____3206 =
                let uu____3211 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____3211  in
              let uu____3214 =
                let uu____3221 =
                  let uu____3226 = FStar_TypeChecker_NBETerm.embed e_term ty
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____3226  in
                let uu____3227 =
                  let uu____3234 =
                    let uu____3239 = FStar_TypeChecker_NBETerm.embed e_term t
                       in
                    FStar_TypeChecker_NBETerm.as_arg uu____3239  in
                  [uu____3234]  in
                uu____3221 :: uu____3227  in
              uu____3206 :: uu____3214  in
            uu____3193 :: uu____3199  in
          uu____3180 :: uu____3186  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____3173
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3266 =
          let uu____3273 =
            let uu____3278 = FStar_TypeChecker_NBETerm.embed e_string_list nm
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3278  in
          let uu____3281 =
            let uu____3288 =
              let uu____3293 = FStar_TypeChecker_NBETerm.embed e_term ty  in
              FStar_TypeChecker_NBETerm.as_arg uu____3293  in
            [uu____3288]  in
          uu____3273 :: uu____3281  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____3266
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____3323 =
          let uu____3330 =
            let uu____3335 = FStar_TypeChecker_NBETerm.embed e_string_list nm
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3335  in
          let uu____3338 =
            let uu____3345 =
              let uu____3350 =
                FStar_TypeChecker_NBETerm.embed e_univ_names univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3350  in
            let uu____3353 =
              let uu____3360 =
                let uu____3365 = FStar_TypeChecker_NBETerm.embed e_binders bs
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____3365  in
              let uu____3366 =
                let uu____3373 =
                  let uu____3378 = FStar_TypeChecker_NBETerm.embed e_term t
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____3378  in
                let uu____3379 =
                  let uu____3386 =
                    let uu____3391 =
                      let uu____3392 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____3392 dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____3391  in
                  [uu____3386]  in
                uu____3373 :: uu____3379  in
              uu____3360 :: uu____3366  in
            uu____3345 :: uu____3353  in
          uu____3330 :: uu____3338  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____3323
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3444,(dcs,uu____3446)::(t1,uu____3448)::(bs,uu____3450)::
         (us,uu____3452)::(nm,uu____3454)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____3489 = FStar_TypeChecker_NBETerm.unembed e_string_list nm
           in
        FStar_Util.bind_opt uu____3489
          (fun nm1  ->
             let uu____3503 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names us  in
             FStar_Util.bind_opt uu____3503
               (fun us1  ->
                  let uu____3517 =
                    FStar_TypeChecker_NBETerm.unembed e_binders bs  in
                  FStar_Util.bind_opt uu____3517
                    (fun bs1  ->
                       let uu____3523 =
                         FStar_TypeChecker_NBETerm.unembed e_term t1  in
                       FStar_Util.bind_opt uu____3523
                         (fun t2  ->
                            let uu____3529 =
                              let uu____3536 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____3536
                                dcs
                               in
                            FStar_Util.bind_opt uu____3529
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3568,(t1,uu____3570)::(ty,uu____3572)::(univs1,uu____3574)::
         (fvar1,uu____3576)::(r,uu____3578)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____3613 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            r
           in
        FStar_Util.bind_opt uu____3613
          (fun r1  ->
             let uu____3619 = FStar_TypeChecker_NBETerm.unembed e_fv fvar1
                in
             FStar_Util.bind_opt uu____3619
               (fun fvar2  ->
                  let uu____3625 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names univs1  in
                  FStar_Util.bind_opt uu____3625
                    (fun univs2  ->
                       let uu____3639 =
                         FStar_TypeChecker_NBETerm.unembed e_term ty  in
                       FStar_Util.bind_opt uu____3639
                         (fun ty1  ->
                            let uu____3645 =
                              FStar_TypeChecker_NBETerm.unembed e_term t1  in
                            FStar_Util.bind_opt uu____3645
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _0_44  ->
                                      FStar_Pervasives_Native.Some _0_44)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3655,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____3670 ->
        ((let uu____3672 =
            let uu____3677 =
              let uu____3678 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____3678
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3677)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3672);
         FStar_Pervasives_Native.None)
     in
  let uu____3679 = mkFV FStar_Reflection_Data.fstar_refl_sigelt_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt_view unembed_sigelt_view
    uu____3679
  
let (e_exp : FStar_Reflection_Data.exp FStar_TypeChecker_NBETerm.embedding) =
  let rec embed_exp e =
    match e with
    | FStar_Reflection_Data.Unit  ->
        mkConstruct FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Var i ->
        let uu____3697 =
          let uu____3704 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____3704]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____3697
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____3719 =
          let uu____3726 =
            let uu____3731 = embed_exp e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____3731  in
          let uu____3732 =
            let uu____3739 =
              let uu____3744 = embed_exp e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____3744  in
            [uu____3739]  in
          uu____3726 :: uu____3732  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____3719
     in
  let rec unembed_exp t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3768,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3784,(i,uu____3786)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____3805 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int i
           in
        FStar_Util.bind_opt uu____3805
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3813,(e2,uu____3815)::(e1,uu____3817)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____3840 = unembed_exp e1  in
        FStar_Util.bind_opt uu____3840
          (fun e11  ->
             let uu____3846 = unembed_exp e2  in
             FStar_Util.bind_opt uu____3846
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____3853 ->
        ((let uu____3855 =
            let uu____3860 =
              let uu____3861 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____3861  in
            (FStar_Errors.Warning_NotEmbedded, uu____3860)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3855);
         FStar_Pervasives_Native.None)
     in
  let uu____3862 = mkFV FStar_Reflection_Data.fstar_refl_exp_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_exp unembed_exp uu____3862 
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_bv e_aqualv 
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding) = e_term 
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_attribute 