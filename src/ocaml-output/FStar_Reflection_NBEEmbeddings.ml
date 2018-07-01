open Prims
let mk_lazy :
  'Auu____9 .
    'Auu____9 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.lazy_kind -> FStar_TypeChecker_NBETerm.t
  =
  fun obj  ->
    fun ty  ->
      fun kind  ->
        let li =
          let uu____30 = FStar_Dyn.mkdyn obj  in
          {
            FStar_Syntax_Syntax.blob = uu____30;
            FStar_Syntax_Syntax.lkind = kind;
            FStar_Syntax_Syntax.typ = ty;
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
    | FStar_TypeChecker_NBETerm.Lazy li when
        li.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____50 = FStar_Dyn.undyn li.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____50
    | uu____53 ->
        ((let uu____55 =
            let uu____60 =
              let uu____61 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____61  in
            (FStar_Errors.Warning_NotEmbedded, uu____60)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____55);
         FStar_Pervasives_Native.None)
     in
  let uu____62 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_bv_fv []
      []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_bv unembed_bv uu____62 
let (e_binder :
  FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding) =
  let embed_binder b =
    mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder
     in
  let unembed_binder t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy li when
        li.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____86 = FStar_Dyn.undyn li.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____86
    | uu____87 ->
        ((let uu____89 =
            let uu____94 =
              let uu____95 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____95  in
            (FStar_Errors.Warning_NotEmbedded, uu____94)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____89);
         FStar_Pervasives_Native.None)
     in
  let uu____96 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_binder_fv
      [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_binder unembed_binder uu____96 
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
          let uu____146 = f x  in
          FStar_Util.bind_opt uu____146
            (fun x1  ->
               let uu____154 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____154
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
      | uu____217 -> FStar_Pervasives_Native.None  in
    let uu____218 =
      FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_term_fv
        [] []
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____218
    }
  
let (e_term : FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding) =
  e_term_aq [] 
let (e_aqualv :
  FStar_Reflection_Data.aqualv FStar_TypeChecker_NBETerm.embedding) =
  let embed_aqualv q =
    match q with
    | FStar_Reflection_Data.Q_Explicit  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Q_Implicit  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Q_Meta t ->
        let uu____250 =
          let uu____251 =
            let uu____256 = FStar_TypeChecker_NBETerm.embed e_term t  in
            FStar_TypeChecker_NBETerm.as_arg uu____256  in
          [uu____251]  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv []
          uu____250
     in
  let unembed_aqualv t =
    match t with
    | FStar_TypeChecker_NBETerm.FV (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
    | FStar_TypeChecker_NBETerm.FV (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
    | FStar_TypeChecker_NBETerm.FV (fv,[],(t1,uu____303)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____320 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
        FStar_Util.bind_opt uu____320
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____325 ->
        ((let uu____327 =
            let uu____332 =
              let uu____333 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____333  in
            (FStar_Errors.Warning_NotEmbedded, uu____332)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____327);
         FStar_Pervasives_Native.None)
     in
  let uu____334 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_aqualv_fv
      [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____334 
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
    | FStar_TypeChecker_NBETerm.Lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____360 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____360
    | uu____361 ->
        ((let uu____363 =
            let uu____368 =
              let uu____369 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____369  in
            (FStar_Errors.Warning_NotEmbedded, uu____368)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____363);
         FStar_Pervasives_Native.None)
     in
  let uu____370 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_fv_fv []
      []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_fv unembed_fv uu____370 
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp c =
    mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp
     in
  let unembed_comp t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____394 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____394
    | uu____395 ->
        ((let uu____397 =
            let uu____402 =
              let uu____403 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____403  in
            (FStar_Errors.Warning_NotEmbedded, uu____402)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____397);
         FStar_Pervasives_Native.None)
     in
  let uu____404 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_comp_fv
      [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp unembed_comp uu____404 
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env e =
    mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env
     in
  let unembed_env t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____428 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____428
    | uu____429 ->
        ((let uu____431 =
            let uu____436 =
              let uu____437 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____437  in
            (FStar_Errors.Warning_NotEmbedded, uu____436)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____431);
         FStar_Pervasives_Native.None)
     in
  let uu____438 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_env_fv []
      []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_env unembed_env uu____438 
let (e_const :
  FStar_Reflection_Data.vconst FStar_TypeChecker_NBETerm.embedding) =
  let embed_const c =
    match c with
    | FStar_Reflection_Data.C_Unit  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_True  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_False  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.C_Int i ->
        let uu____464 =
          let uu____465 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____465]  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv []
          uu____464
    | FStar_Reflection_Data.C_String s ->
        let uu____479 =
          let uu____480 =
            let uu____485 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____485  in
          [uu____480]  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____479
     in
  let unembed_const t =
    match t with
    | FStar_TypeChecker_NBETerm.FV (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
    | FStar_TypeChecker_NBETerm.FV (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
    | FStar_TypeChecker_NBETerm.FV (fv,[],[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
    | FStar_TypeChecker_NBETerm.FV (fv,[],(i,uu____545)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____562 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int i
           in
        FStar_Util.bind_opt uu____562
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.FV (fv,[],(s,uu____571)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____588 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string s
           in
        FStar_Util.bind_opt uu____588
          (fun s1  ->
             FStar_All.pipe_left
               (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
               (FStar_Reflection_Data.C_String s1))
    | uu____595 ->
        ((let uu____597 =
            let uu____602 =
              let uu____603 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____603  in
            (FStar_Errors.Warning_NotEmbedded, uu____602)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____597);
         FStar_Pervasives_Native.None)
     in
  let uu____604 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_vconst_fv
      [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_const unembed_const uu____604 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____615  ->
    let rec embed_pattern p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____623 =
            let uu____624 =
              let uu____629 = FStar_TypeChecker_NBETerm.embed e_const c  in
              FStar_TypeChecker_NBETerm.as_arg uu____629  in
            [uu____624]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____623
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____644 =
            let uu____645 =
              let uu____650 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____650  in
            let uu____651 =
              let uu____658 =
                let uu____663 =
                  let uu____664 =
                    let uu____669 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____669  in
                  FStar_TypeChecker_NBETerm.embed uu____664 ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____663  in
              [uu____658]  in
            uu____645 :: uu____651  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____644
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____687 =
            let uu____688 =
              let uu____693 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____693  in
            [uu____688]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____687
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____703 =
            let uu____704 =
              let uu____709 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____709  in
            [uu____704]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____703
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____720 =
            let uu____721 =
              let uu____726 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____726  in
            let uu____727 =
              let uu____734 =
                let uu____739 = FStar_TypeChecker_NBETerm.embed e_term t  in
                FStar_TypeChecker_NBETerm.as_arg uu____739  in
              [uu____734]  in
            uu____721 :: uu____727  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____720
       in
    let rec unembed_pattern t =
      match t with
      | FStar_TypeChecker_NBETerm.FV (fv,[],(c,uu____764)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____781 = FStar_TypeChecker_NBETerm.unembed e_const c  in
          FStar_Util.bind_opt uu____781
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.FV
          (fv,[],(f,uu____790)::(ps,uu____792)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____813 = FStar_TypeChecker_NBETerm.unembed e_fv f  in
          FStar_Util.bind_opt uu____813
            (fun f1  ->
               let uu____819 =
                 let uu____824 =
                   let uu____829 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____829  in
                 FStar_TypeChecker_NBETerm.unembed uu____824 ps  in
               FStar_Util.bind_opt uu____819
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.FV (fv,[],(bv,uu____846)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____863 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____863
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.FV (fv,[],(bv,uu____872)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____889 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____889
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.FV
          (fv,[],(bv,uu____898)::(t1,uu____900)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____921 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____921
            (fun bv1  ->
               let uu____927 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____927
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____934 ->
          ((let uu____936 =
              let uu____941 =
                let uu____942 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____942
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____941)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____936);
           FStar_Pervasives_Native.None)
       in
    let uu____943 =
      FStar_TypeChecker_NBETerm.mkFV
        FStar_Reflection_Data.fstar_refl_pattern_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_pattern unembed_pattern uu____943
  
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
    let uu____985 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____985
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1019 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1019 e_aqualv
  
let rec unlazy_as_t :
  'Auu____1028 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1028
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.typ = uu____1041;
            FStar_Syntax_Syntax.rng = uu____1042;_}
          when k = k' -> FStar_Dyn.undyn v1
      | uu____1045 -> failwith "Not a Lazy of the expected kind (NBE)"
  
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
          let uu____1080 =
            let uu____1081 =
              let uu____1086 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1086  in
            [uu____1081]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1080
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1096 =
            let uu____1097 =
              let uu____1102 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1102  in
            [uu____1097]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1096
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1112 =
            let uu____1113 =
              let uu____1118 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1118  in
            [uu____1113]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1112
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1129 =
            let uu____1130 =
              let uu____1135 =
                let uu____1136 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1136 hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1135  in
            let uu____1139 =
              let uu____1146 =
                let uu____1151 =
                  let uu____1152 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1152 a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1151  in
              [uu____1146]  in
            uu____1130 :: uu____1139  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1129
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1177 =
            let uu____1178 =
              let uu____1183 = FStar_TypeChecker_NBETerm.embed e_binder b  in
              FStar_TypeChecker_NBETerm.as_arg uu____1183  in
            let uu____1184 =
              let uu____1191 =
                let uu____1196 =
                  let uu____1197 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1197 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1196  in
              [uu____1191]  in
            uu____1178 :: uu____1184  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1177
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1214 =
            let uu____1215 =
              let uu____1220 = FStar_TypeChecker_NBETerm.embed e_binder b  in
              FStar_TypeChecker_NBETerm.as_arg uu____1220  in
            let uu____1221 =
              let uu____1228 =
                let uu____1233 = FStar_TypeChecker_NBETerm.embed e_comp c  in
                FStar_TypeChecker_NBETerm.as_arg uu____1233  in
              [uu____1228]  in
            uu____1215 :: uu____1221  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1214
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1247 =
            let uu____1248 =
              let uu____1253 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1253  in
            [uu____1248]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1247
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____1264 =
            let uu____1265 =
              let uu____1270 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1270  in
            let uu____1271 =
              let uu____1278 =
                let uu____1283 =
                  let uu____1284 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1284 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1283  in
              [uu____1278]  in
            uu____1265 :: uu____1271  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1264
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1300 =
            let uu____1301 =
              let uu____1306 = FStar_TypeChecker_NBETerm.embed e_const c  in
              FStar_TypeChecker_NBETerm.as_arg uu____1306  in
            [uu____1301]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1300
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____1317 =
            let uu____1318 =
              let uu____1323 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1323  in
            let uu____1324 =
              let uu____1331 =
                let uu____1336 =
                  mk_lazy (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1336  in
              [uu____1331]  in
            uu____1318 :: uu____1324  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____1317
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1357 =
            let uu____1358 =
              let uu____1363 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1363  in
            let uu____1364 =
              let uu____1371 =
                let uu____1376 = FStar_TypeChecker_NBETerm.embed e_bv b  in
                FStar_TypeChecker_NBETerm.as_arg uu____1376  in
              let uu____1377 =
                let uu____1384 =
                  let uu____1389 =
                    let uu____1390 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____1390 t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1389  in
                let uu____1393 =
                  let uu____1400 =
                    let uu____1405 =
                      let uu____1406 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____1406 t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____1405  in
                  [uu____1400]  in
                uu____1384 :: uu____1393  in
              uu____1371 :: uu____1377  in
            uu____1358 :: uu____1364  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____1357
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____1435 =
            let uu____1436 =
              let uu____1441 =
                let uu____1442 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1442 t  in
              FStar_TypeChecker_NBETerm.as_arg uu____1441  in
            let uu____1445 =
              let uu____1452 =
                let uu____1457 =
                  let uu____1458 =
                    let uu____1467 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____1467  in
                  FStar_TypeChecker_NBETerm.embed uu____1458 brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____1457  in
              [uu____1452]  in
            uu____1436 :: uu____1445  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____1435
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____1503 =
            let uu____1504 =
              let uu____1509 =
                let uu____1510 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1510 e  in
              FStar_TypeChecker_NBETerm.as_arg uu____1509  in
            let uu____1513 =
              let uu____1520 =
                let uu____1525 =
                  let uu____1526 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1526 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1525  in
              let uu____1529 =
                let uu____1536 =
                  let uu____1541 =
                    let uu____1542 =
                      let uu____1547 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____1547  in
                    FStar_TypeChecker_NBETerm.embed uu____1542 tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1541  in
                [uu____1536]  in
              uu____1520 :: uu____1529  in
            uu____1504 :: uu____1513  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____1503
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____1575 =
            let uu____1576 =
              let uu____1581 =
                let uu____1582 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1582 e  in
              FStar_TypeChecker_NBETerm.as_arg uu____1581  in
            let uu____1585 =
              let uu____1592 =
                let uu____1597 = FStar_TypeChecker_NBETerm.embed e_comp c  in
                FStar_TypeChecker_NBETerm.as_arg uu____1597  in
              let uu____1598 =
                let uu____1605 =
                  let uu____1610 =
                    let uu____1611 =
                      let uu____1616 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____1616  in
                    FStar_TypeChecker_NBETerm.embed uu____1611 tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1610  in
                [uu____1605]  in
              uu____1592 :: uu____1598  in
            uu____1576 :: uu____1585  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____1575
      | FStar_Reflection_Data.Tv_Unknown  ->
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view t =
      match t with
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1652,(b,uu____1654)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____1673 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1673
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1681,(b,uu____1683)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____1702 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1702
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1710,(f,uu____1712)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____1731 = FStar_TypeChecker_NBETerm.unembed e_fv f  in
          FStar_Util.bind_opt uu____1731
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1739,(l,uu____1741)::(r,uu____1743)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____1766 = FStar_TypeChecker_NBETerm.unembed e_term l  in
          FStar_Util.bind_opt uu____1766
            (fun l1  ->
               let uu____1772 = FStar_TypeChecker_NBETerm.unembed e_argv r
                  in
               FStar_Util.bind_opt uu____1772
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1780,(b,uu____1782)::(t1,uu____1784)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____1807 = FStar_TypeChecker_NBETerm.unembed e_binder b  in
          FStar_Util.bind_opt uu____1807
            (fun b1  ->
               let uu____1813 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____1813
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1821,(b,uu____1823)::(t1,uu____1825)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____1848 = FStar_TypeChecker_NBETerm.unembed e_binder b  in
          FStar_Util.bind_opt uu____1848
            (fun b1  ->
               let uu____1854 = FStar_TypeChecker_NBETerm.unembed e_comp t1
                  in
               FStar_Util.bind_opt uu____1854
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1862,(u,uu____1864)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____1883 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit u
             in
          FStar_Util.bind_opt uu____1883
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1891,(b,uu____1893)::(t1,uu____1895)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____1918 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1918
            (fun b1  ->
               let uu____1924 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____1924
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1932,(c,uu____1934)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____1953 = FStar_TypeChecker_NBETerm.unembed e_const c  in
          FStar_Util.bind_opt uu____1953
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1961,(u,uu____1963)::(l,uu____1965)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____1988 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              u
             in
          FStar_Util.bind_opt uu____1988
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1998,(r,uu____2000)::(b,uu____2002)::(t1,uu____2004)::
           (t2,uu____2006)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2037 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool r
             in
          FStar_Util.bind_opt uu____2037
            (fun r1  ->
               let uu____2043 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
               FStar_Util.bind_opt uu____2043
                 (fun b1  ->
                    let uu____2049 =
                      FStar_TypeChecker_NBETerm.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2049
                      (fun t11  ->
                         let uu____2055 =
                           FStar_TypeChecker_NBETerm.unembed e_term t2  in
                         FStar_Util.bind_opt uu____2055
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _0_34  ->
                                   FStar_Pervasives_Native.Some _0_34)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____2063,(t1,uu____2065)::(brs,uu____2067)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2090 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
          FStar_Util.bind_opt uu____2090
            (fun t2  ->
               let uu____2096 =
                 let uu____2101 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2101 brs  in
               FStar_Util.bind_opt uu____2096
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____2119,(e,uu____2121)::(t1,uu____2123)::(tacopt,uu____2125)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2152 = FStar_TypeChecker_NBETerm.unembed e_term e  in
          FStar_Util.bind_opt uu____2152
            (fun e1  ->
               let uu____2158 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____2158
                 (fun t2  ->
                    let uu____2164 =
                      let uu____2169 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2169 tacopt  in
                    FStar_Util.bind_opt uu____2164
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____2187,(e,uu____2189)::(c,uu____2191)::(tacopt,uu____2193)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____2220 = FStar_TypeChecker_NBETerm.unembed e_term e  in
          FStar_Util.bind_opt uu____2220
            (fun e1  ->
               let uu____2226 = FStar_TypeChecker_NBETerm.unembed e_comp c
                  in
               FStar_Util.bind_opt uu____2226
                 (fun c1  ->
                    let uu____2232 =
                      let uu____2237 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2237 tacopt  in
                    FStar_Util.bind_opt uu____2232
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____2255,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
            FStar_Reflection_Data.Tv_Unknown
      | uu____2272 ->
          ((let uu____2274 =
              let uu____2279 =
                let uu____2280 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____2280
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2279)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2274);
           FStar_Pervasives_Native.None)
       in
    let uu____2281 =
      FStar_TypeChecker_NBETerm.mkFV
        FStar_Reflection_Data.fstar_refl_term_view_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_term_view unembed_term_view
      uu____2281
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view bvv =
    let uu____2304 =
      let uu____2305 =
        let uu____2310 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____2310  in
      let uu____2311 =
        let uu____2318 =
          let uu____2323 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____2323  in
        let uu____2324 =
          let uu____2331 =
            let uu____2336 =
              FStar_TypeChecker_NBETerm.embed e_term
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2336  in
          [uu____2331]  in
        uu____2318 :: uu____2324  in
      uu____2305 :: uu____2311  in
    FStar_TypeChecker_NBETerm.mkFV
      FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv [] uu____2304
     in
  let unembed_bv_view t =
    match t with
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____2364,(nm,uu____2366)::(idx,uu____2368)::(s,uu____2370)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____2397 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string nm
           in
        FStar_Util.bind_opt uu____2397
          (fun nm1  ->
             let uu____2403 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int idx
                in
             FStar_Util.bind_opt uu____2403
               (fun idx1  ->
                  let uu____2409 = FStar_TypeChecker_NBETerm.unembed e_term s
                     in
                  FStar_Util.bind_opt uu____2409
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____2416 ->
        ((let uu____2418 =
            let uu____2423 =
              let uu____2424 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____2424  in
            (FStar_Errors.Warning_NotEmbedded, uu____2423)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2418);
         FStar_Pervasives_Native.None)
     in
  let uu____2425 =
    FStar_TypeChecker_NBETerm.mkFV
      FStar_Reflection_Data.fstar_refl_bv_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_bv_view unembed_bv_view uu____2425 
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____2444 =
          let uu____2445 =
            let uu____2450 = FStar_TypeChecker_NBETerm.embed e_term t  in
            FStar_TypeChecker_NBETerm.as_arg uu____2450  in
          let uu____2451 =
            let uu____2458 =
              let uu____2463 =
                let uu____2464 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____2464 md  in
              FStar_TypeChecker_NBETerm.as_arg uu____2463  in
            [uu____2458]  in
          uu____2445 :: uu____2451  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____2444
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____2488 =
          let uu____2489 =
            let uu____2494 = FStar_TypeChecker_NBETerm.embed e_term pre  in
            FStar_TypeChecker_NBETerm.as_arg uu____2494  in
          let uu____2495 =
            let uu____2502 =
              let uu____2507 = FStar_TypeChecker_NBETerm.embed e_term post1
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2507  in
            [uu____2502]  in
          uu____2489 :: uu____2495  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____2488
    | FStar_Reflection_Data.C_Unknown  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view t =
    match t with
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____2535,(t1,uu____2537)::(md,uu____2539)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____2562 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
        FStar_Util.bind_opt uu____2562
          (fun t2  ->
             let uu____2568 =
               let uu____2573 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____2573 md  in
             FStar_Util.bind_opt uu____2568
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____2591,(pre,uu____2593)::(post,uu____2595)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____2618 = FStar_TypeChecker_NBETerm.unembed e_term pre  in
        FStar_Util.bind_opt uu____2618
          (fun pre1  ->
             let uu____2624 = FStar_TypeChecker_NBETerm.unembed e_term post
                in
             FStar_Util.bind_opt uu____2624
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.FV (fv,uu____2632,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
          FStar_Reflection_Data.C_Unknown
    | uu____2649 ->
        ((let uu____2651 =
            let uu____2656 =
              let uu____2657 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____2657
               in
            (FStar_Errors.Warning_NotEmbedded, uu____2656)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2651);
         FStar_Pervasives_Native.None)
     in
  let uu____2658 =
    FStar_TypeChecker_NBETerm.mkFV
      FStar_Reflection_Data.fstar_refl_comp_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp_view unembed_comp_view
    uu____2658
  
let (e_order : FStar_Order.order FStar_TypeChecker_NBETerm.embedding) =
  let embed_order o =
    match o with
    | FStar_Order.Lt  ->
        FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.ord_Lt_fv [] []
    | FStar_Order.Eq  ->
        FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.ord_Eq_fv [] []
    | FStar_Order.Gt  ->
        FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.ord_Gt_fv [] []
     in
  let unembed_order t =
    match t with
    | FStar_TypeChecker_NBETerm.FV (fv,uu____2694,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.FV (fv,uu____2710,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.FV (fv,uu____2726,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____2741 ->
        ((let uu____2743 =
            let uu____2748 =
              let uu____2749 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____2749  in
            (FStar_Errors.Warning_NotEmbedded, uu____2748)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2743);
         FStar_Pervasives_Native.None)
     in
  let uu____2750 =
    let uu____2751 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_TypeChecker_NBETerm.mkFV uu____2751 [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_order unembed_order uu____2750 
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding) =
  let embed_sigelt se =
    mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt
     in
  let unembed_sigelt t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____2775 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2775
    | uu____2776 ->
        ((let uu____2778 =
            let uu____2783 =
              let uu____2784 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____2784  in
            (FStar_Errors.Warning_NotEmbedded, uu____2783)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2778);
         FStar_Pervasives_Native.None)
     in
  let uu____2785 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_sigelt_fv
      [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt unembed_sigelt uu____2785 
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string
     in
  let embed_ident i =
    let uu____2807 =
      let uu____2812 = FStar_Ident.range_of_id i  in
      let uu____2813 = FStar_Ident.text_of_id i  in (uu____2812, uu____2813)
       in
    FStar_TypeChecker_NBETerm.embed repr uu____2807  in
  let unembed_ident t =
    let uu____2828 = FStar_TypeChecker_NBETerm.unembed repr t  in
    match uu____2828 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____2847 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____2847
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____2852 =
    let uu____2853 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____2854 =
      let uu____2855 =
        let uu____2860 =
          let uu____2861 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_TypeChecker_NBETerm.mkFV uu____2861 [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____2860  in
      let uu____2866 =
        let uu____2873 =
          let uu____2878 =
            let uu____2879 =
              FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            FStar_TypeChecker_NBETerm.mkFV uu____2879 [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____2878  in
        [uu____2873]  in
      uu____2855 :: uu____2866  in
    FStar_TypeChecker_NBETerm.mkFV uu____2853
      [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2854
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____2852 
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
        let uu____2923 =
          let uu____2924 =
            let uu____2929 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2929  in
          let uu____2930 =
            let uu____2937 =
              let uu____2942 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____2942  in
            let uu____2943 =
              let uu____2950 =
                let uu____2955 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____2955  in
              let uu____2958 =
                let uu____2965 =
                  let uu____2970 = FStar_TypeChecker_NBETerm.embed e_term ty
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____2970  in
                let uu____2971 =
                  let uu____2978 =
                    let uu____2983 = FStar_TypeChecker_NBETerm.embed e_term t
                       in
                    FStar_TypeChecker_NBETerm.as_arg uu____2983  in
                  [uu____2978]  in
                uu____2965 :: uu____2971  in
              uu____2950 :: uu____2958  in
            uu____2937 :: uu____2943  in
          uu____2924 :: uu____2930  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv []
          uu____2923
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3010 =
          let uu____3011 =
            let uu____3016 = FStar_TypeChecker_NBETerm.embed e_string_list nm
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3016  in
          let uu____3019 =
            let uu____3026 =
              let uu____3031 = FStar_TypeChecker_NBETerm.embed e_term ty  in
              FStar_TypeChecker_NBETerm.as_arg uu____3031  in
            [uu____3026]  in
          uu____3011 :: uu____3019  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____3010
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____3061 =
          let uu____3062 =
            let uu____3067 = FStar_TypeChecker_NBETerm.embed e_string_list nm
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3067  in
          let uu____3070 =
            let uu____3077 =
              let uu____3082 =
                FStar_TypeChecker_NBETerm.embed e_univ_names univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3082  in
            let uu____3085 =
              let uu____3092 =
                let uu____3097 = FStar_TypeChecker_NBETerm.embed e_binders bs
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____3097  in
              let uu____3098 =
                let uu____3105 =
                  let uu____3110 = FStar_TypeChecker_NBETerm.embed e_term t
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____3110  in
                let uu____3111 =
                  let uu____3118 =
                    let uu____3123 =
                      let uu____3124 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____3124 dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____3123  in
                  [uu____3118]  in
                uu____3105 :: uu____3111  in
              uu____3092 :: uu____3098  in
            uu____3077 :: uu____3085  in
          uu____3062 :: uu____3070  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____3061
    | FStar_Reflection_Data.Unk  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv [] []
     in
  let unembed_sigelt_view t =
    match t with
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____3176,(nm,uu____3178)::(us,uu____3180)::(bs,uu____3182)::
         (t1,uu____3184)::(dcs,uu____3186)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____3221 = FStar_TypeChecker_NBETerm.unembed e_string_list nm
           in
        FStar_Util.bind_opt uu____3221
          (fun nm1  ->
             let uu____3235 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names us  in
             FStar_Util.bind_opt uu____3235
               (fun us1  ->
                  let uu____3249 =
                    FStar_TypeChecker_NBETerm.unembed e_binders bs  in
                  FStar_Util.bind_opt uu____3249
                    (fun bs1  ->
                       let uu____3255 =
                         FStar_TypeChecker_NBETerm.unembed e_term t1  in
                       FStar_Util.bind_opt uu____3255
                         (fun t2  ->
                            let uu____3261 =
                              let uu____3268 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____3268
                                dcs
                               in
                            FStar_Util.bind_opt uu____3261
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____3300,(r,uu____3302)::(fvar1,uu____3304)::(univs1,uu____3306)::
         (ty,uu____3308)::(t1,uu____3310)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____3345 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            r
           in
        FStar_Util.bind_opt uu____3345
          (fun r1  ->
             let uu____3351 = FStar_TypeChecker_NBETerm.unembed e_fv fvar1
                in
             FStar_Util.bind_opt uu____3351
               (fun fvar2  ->
                  let uu____3357 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names univs1  in
                  FStar_Util.bind_opt uu____3357
                    (fun univs2  ->
                       let uu____3371 =
                         FStar_TypeChecker_NBETerm.unembed e_term ty  in
                       FStar_Util.bind_opt uu____3371
                         (fun ty1  ->
                            let uu____3377 =
                              FStar_TypeChecker_NBETerm.unembed e_term t1  in
                            FStar_Util.bind_opt uu____3377
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _0_44  ->
                                      FStar_Pervasives_Native.Some _0_44)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.FV (fv,uu____3387,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____3402 ->
        ((let uu____3404 =
            let uu____3409 =
              let uu____3410 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____3410
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3409)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3404);
         FStar_Pervasives_Native.None)
     in
  let uu____3411 =
    FStar_TypeChecker_NBETerm.mkFV
      FStar_Reflection_Data.fstar_refl_sigelt_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt_view unembed_sigelt_view
    uu____3411
  
let (e_exp : FStar_Reflection_Data.exp FStar_TypeChecker_NBETerm.embedding) =
  let rec embed_exp e =
    match e with
    | FStar_Reflection_Data.Unit  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Var i ->
        let uu____3429 =
          let uu____3430 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____3430]  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv []
          uu____3429
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____3445 =
          let uu____3446 =
            let uu____3451 = embed_exp e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____3451  in
          let uu____3452 =
            let uu____3459 =
              let uu____3464 = embed_exp e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____3464  in
            [uu____3459]  in
          uu____3446 :: uu____3452  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv []
          uu____3445
     in
  let rec unembed_exp t =
    match t with
    | FStar_TypeChecker_NBETerm.FV (fv,uu____3488,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.FV (fv,uu____3504,(i,uu____3506)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____3525 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int i
           in
        FStar_Util.bind_opt uu____3525
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____3533,(e1,uu____3535)::(e2,uu____3537)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____3560 = unembed_exp e1  in
        FStar_Util.bind_opt uu____3560
          (fun e11  ->
             let uu____3566 = unembed_exp e2  in
             FStar_Util.bind_opt uu____3566
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____3573 ->
        ((let uu____3575 =
            let uu____3580 =
              let uu____3581 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____3581  in
            (FStar_Errors.Warning_NotEmbedded, uu____3580)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3575);
         FStar_Pervasives_Native.None)
     in
  let uu____3582 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_exp_fv []
      []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_exp unembed_exp uu____3582 
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_bv e_aqualv 
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding) = e_term 
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_attribute 