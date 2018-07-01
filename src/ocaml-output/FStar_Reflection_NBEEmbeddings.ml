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
        let uu____120 = FStar_Dyn.undyn li.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____120
    | uu____123 ->
        ((let uu____125 =
            let uu____130 =
              let uu____131 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____131  in
            (FStar_Errors.Warning_NotEmbedded, uu____130)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____125);
         FStar_Pervasives_Native.None)
     in
  let uu____132 = mkFV FStar_Reflection_Data.fstar_refl_bv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_bv unembed_bv uu____132 
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
        let uu____156 = FStar_Dyn.undyn li.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____156
    | uu____157 ->
        ((let uu____159 =
            let uu____164 =
              let uu____165 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____165  in
            (FStar_Errors.Warning_NotEmbedded, uu____164)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____159);
         FStar_Pervasives_Native.None)
     in
  let uu____166 = mkFV FStar_Reflection_Data.fstar_refl_binder_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_binder unembed_binder uu____166 
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
          let uu____216 = f x  in
          FStar_Util.bind_opt uu____216
            (fun x1  ->
               let uu____224 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____224
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
      | uu____287 -> FStar_Pervasives_Native.None  in
    let uu____288 = mkFV FStar_Reflection_Data.fstar_refl_term_fv [] []  in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____288
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
        let uu____320 =
          let uu____327 =
            let uu____332 = FStar_TypeChecker_NBETerm.embed e_term t  in
            FStar_TypeChecker_NBETerm.as_arg uu____332  in
          [uu____327]  in
        mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv
          [] uu____320
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(t1,uu____379)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____396 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
        FStar_Util.bind_opt uu____396
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____401 ->
        ((let uu____403 =
            let uu____408 =
              let uu____409 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____409  in
            (FStar_Errors.Warning_NotEmbedded, uu____408)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____403);
         FStar_Pervasives_Native.None)
     in
  let uu____410 =
    mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____410 
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
        let uu____436 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____436
    | uu____437 ->
        ((let uu____439 =
            let uu____444 =
              let uu____445 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____445  in
            (FStar_Errors.Warning_NotEmbedded, uu____444)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____439);
         FStar_Pervasives_Native.None)
     in
  let uu____446 = mkFV FStar_Reflection_Data.fstar_refl_fv_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_fv unembed_fv uu____446 
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp c =
    mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp
     in
  let unembed_comp t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____470 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____470
    | uu____471 ->
        ((let uu____473 =
            let uu____478 =
              let uu____479 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____479  in
            (FStar_Errors.Warning_NotEmbedded, uu____478)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____473);
         FStar_Pervasives_Native.None)
     in
  let uu____480 = mkFV FStar_Reflection_Data.fstar_refl_comp_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp unembed_comp uu____480 
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env e =
    mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env
     in
  let unembed_env t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____504 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____504
    | uu____505 ->
        ((let uu____507 =
            let uu____512 =
              let uu____513 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____513  in
            (FStar_Errors.Warning_NotEmbedded, uu____512)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____507);
         FStar_Pervasives_Native.None)
     in
  let uu____514 = mkFV FStar_Reflection_Data.fstar_refl_env_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_env unembed_env uu____514 
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
        let uu____540 =
          let uu____547 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____547]  in
        mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv
          [] uu____540
    | FStar_Reflection_Data.C_String s ->
        let uu____561 =
          let uu____568 =
            let uu____573 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____573  in
          [uu____568]  in
        mkConstruct
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____561
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
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(i,uu____633)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____650 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int i
           in
        FStar_Util.bind_opt uu____650
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.Construct (fv,[],(s,uu____659)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____676 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string s
           in
        FStar_Util.bind_opt uu____676
          (fun s1  ->
             FStar_All.pipe_left
               (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
               (FStar_Reflection_Data.C_String s1))
    | uu____683 ->
        ((let uu____685 =
            let uu____690 =
              let uu____691 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____691  in
            (FStar_Errors.Warning_NotEmbedded, uu____690)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____685);
         FStar_Pervasives_Native.None)
     in
  let uu____692 = mkFV FStar_Reflection_Data.fstar_refl_vconst_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_const unembed_const uu____692 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____703  ->
    let rec embed_pattern p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____711 =
            let uu____718 =
              let uu____723 = FStar_TypeChecker_NBETerm.embed e_const c  in
              FStar_TypeChecker_NBETerm.as_arg uu____723  in
            [uu____718]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____711
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____738 =
            let uu____745 =
              let uu____750 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____750  in
            let uu____751 =
              let uu____758 =
                let uu____763 =
                  let uu____764 =
                    let uu____769 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____769  in
                  FStar_TypeChecker_NBETerm.embed uu____764 ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____763  in
              [uu____758]  in
            uu____745 :: uu____751  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____738
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____787 =
            let uu____794 =
              let uu____799 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____799  in
            [uu____794]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____787
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____809 =
            let uu____816 =
              let uu____821 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____821  in
            [uu____816]  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____809
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____832 =
            let uu____839 =
              let uu____844 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____844  in
            let uu____845 =
              let uu____852 =
                let uu____857 = FStar_TypeChecker_NBETerm.embed e_term t  in
                FStar_TypeChecker_NBETerm.as_arg uu____857  in
              [uu____852]  in
            uu____839 :: uu____845  in
          mkConstruct
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____832
       in
    let rec unembed_pattern t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(c,uu____882)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____899 = FStar_TypeChecker_NBETerm.unembed e_const c  in
          FStar_Util.bind_opt uu____899
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(ps,uu____908)::(f,uu____910)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____931 = FStar_TypeChecker_NBETerm.unembed e_fv f  in
          FStar_Util.bind_opt uu____931
            (fun f1  ->
               let uu____937 =
                 let uu____942 =
                   let uu____947 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____947  in
                 FStar_TypeChecker_NBETerm.unembed uu____942 ps  in
               FStar_Util.bind_opt uu____937
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____964)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____981 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____981
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.Construct (fv,[],(bv,uu____990)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____1007 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____1007
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,[],(t1,uu____1016)::(bv,uu____1018)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____1039 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____1039
            (fun bv1  ->
               let uu____1045 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____1045
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____1052 ->
          ((let uu____1054 =
              let uu____1059 =
                let uu____1060 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____1060
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1059)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____1054);
           FStar_Pervasives_Native.None)
       in
    let uu____1061 = mkFV FStar_Reflection_Data.fstar_refl_pattern_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_pattern unembed_pattern uu____1061
  
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
    let uu____1103 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1103
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1137 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1137 e_aqualv
  
let rec unlazy_as_t :
  'Auu____1146 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1146
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.typ = uu____1159;
            FStar_Syntax_Syntax.rng = uu____1160;_}
          when k = k' -> FStar_Dyn.undyn v1
      | uu____1163 -> failwith "Not a Lazy of the expected kind (NBE)"
  
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
          let uu____1198 =
            let uu____1205 =
              let uu____1210 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1210  in
            [uu____1205]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1198
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1220 =
            let uu____1227 =
              let uu____1232 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1232  in
            [uu____1227]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1220
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1242 =
            let uu____1249 =
              let uu____1254 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1254  in
            [uu____1249]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1242
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1265 =
            let uu____1272 =
              let uu____1277 =
                let uu____1278 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1278 hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1277  in
            let uu____1281 =
              let uu____1288 =
                let uu____1293 =
                  let uu____1294 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1294 a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1293  in
              [uu____1288]  in
            uu____1272 :: uu____1281  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1265
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1319 =
            let uu____1326 =
              let uu____1331 = FStar_TypeChecker_NBETerm.embed e_binder b  in
              FStar_TypeChecker_NBETerm.as_arg uu____1331  in
            let uu____1332 =
              let uu____1339 =
                let uu____1344 =
                  let uu____1345 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1345 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1344  in
              [uu____1339]  in
            uu____1326 :: uu____1332  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1319
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1362 =
            let uu____1369 =
              let uu____1374 = FStar_TypeChecker_NBETerm.embed e_binder b  in
              FStar_TypeChecker_NBETerm.as_arg uu____1374  in
            let uu____1375 =
              let uu____1382 =
                let uu____1387 = FStar_TypeChecker_NBETerm.embed e_comp c  in
                FStar_TypeChecker_NBETerm.as_arg uu____1387  in
              [uu____1382]  in
            uu____1369 :: uu____1375  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1362
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1401 =
            let uu____1408 =
              let uu____1413 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1413  in
            [uu____1408]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1401
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____1424 =
            let uu____1431 =
              let uu____1436 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1436  in
            let uu____1437 =
              let uu____1444 =
                let uu____1449 =
                  let uu____1450 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1450 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1449  in
              [uu____1444]  in
            uu____1431 :: uu____1437  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1424
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1466 =
            let uu____1473 =
              let uu____1478 = FStar_TypeChecker_NBETerm.embed e_const c  in
              FStar_TypeChecker_NBETerm.as_arg uu____1478  in
            [uu____1473]  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1466
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____1489 =
            let uu____1496 =
              let uu____1501 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1501  in
            let uu____1502 =
              let uu____1509 =
                let uu____1514 =
                  mk_lazy (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1514  in
              [uu____1509]  in
            uu____1496 :: uu____1502  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____1489
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1535 =
            let uu____1542 =
              let uu____1547 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1547  in
            let uu____1548 =
              let uu____1555 =
                let uu____1560 = FStar_TypeChecker_NBETerm.embed e_bv b  in
                FStar_TypeChecker_NBETerm.as_arg uu____1560  in
              let uu____1561 =
                let uu____1568 =
                  let uu____1573 =
                    let uu____1574 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____1574 t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1573  in
                let uu____1577 =
                  let uu____1584 =
                    let uu____1589 =
                      let uu____1590 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____1590 t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____1589  in
                  [uu____1584]  in
                uu____1568 :: uu____1577  in
              uu____1555 :: uu____1561  in
            uu____1542 :: uu____1548  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____1535
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____1619 =
            let uu____1626 =
              let uu____1631 =
                let uu____1632 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1632 t  in
              FStar_TypeChecker_NBETerm.as_arg uu____1631  in
            let uu____1635 =
              let uu____1642 =
                let uu____1647 =
                  let uu____1648 =
                    let uu____1657 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____1657  in
                  FStar_TypeChecker_NBETerm.embed uu____1648 brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____1647  in
              [uu____1642]  in
            uu____1626 :: uu____1635  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____1619
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____1693 =
            let uu____1700 =
              let uu____1705 =
                let uu____1706 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1706 e  in
              FStar_TypeChecker_NBETerm.as_arg uu____1705  in
            let uu____1709 =
              let uu____1716 =
                let uu____1721 =
                  let uu____1722 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1722 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1721  in
              let uu____1725 =
                let uu____1732 =
                  let uu____1737 =
                    let uu____1738 =
                      let uu____1743 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____1743  in
                    FStar_TypeChecker_NBETerm.embed uu____1738 tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1737  in
                [uu____1732]  in
              uu____1716 :: uu____1725  in
            uu____1700 :: uu____1709  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____1693
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____1771 =
            let uu____1778 =
              let uu____1783 =
                let uu____1784 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1784 e  in
              FStar_TypeChecker_NBETerm.as_arg uu____1783  in
            let uu____1787 =
              let uu____1794 =
                let uu____1799 = FStar_TypeChecker_NBETerm.embed e_comp c  in
                FStar_TypeChecker_NBETerm.as_arg uu____1799  in
              let uu____1800 =
                let uu____1807 =
                  let uu____1812 =
                    let uu____1813 =
                      let uu____1818 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____1818  in
                    FStar_TypeChecker_NBETerm.embed uu____1813 tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1812  in
                [uu____1807]  in
              uu____1794 :: uu____1800  in
            uu____1778 :: uu____1787  in
          mkConstruct
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____1771
      | FStar_Reflection_Data.Tv_Unknown  ->
          mkConstruct
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view t =
      match t with
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1854,(b,uu____1856)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____1875 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1875
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1883,(b,uu____1885)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____1904 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1904
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1912,(f,uu____1914)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____1933 = FStar_TypeChecker_NBETerm.unembed e_fv f  in
          FStar_Util.bind_opt uu____1933
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1941,(r,uu____1943)::(l,uu____1945)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____1968 = FStar_TypeChecker_NBETerm.unembed e_term l  in
          FStar_Util.bind_opt uu____1968
            (fun l1  ->
               let uu____1974 = FStar_TypeChecker_NBETerm.unembed e_argv r
                  in
               FStar_Util.bind_opt uu____1974
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____1982,(t1,uu____1984)::(b,uu____1986)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____2009 = FStar_TypeChecker_NBETerm.unembed e_binder b  in
          FStar_Util.bind_opt uu____2009
            (fun b1  ->
               let uu____2015 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____2015
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2023,(t1,uu____2025)::(b,uu____2027)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____2050 = FStar_TypeChecker_NBETerm.unembed e_binder b  in
          FStar_Util.bind_opt uu____2050
            (fun b1  ->
               let uu____2056 = FStar_TypeChecker_NBETerm.unembed e_comp t1
                  in
               FStar_Util.bind_opt uu____2056
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2064,(u,uu____2066)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____2085 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit u
             in
          FStar_Util.bind_opt uu____2085
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2093,(t1,uu____2095)::(b,uu____2097)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____2120 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____2120
            (fun b1  ->
               let uu____2126 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____2126
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2134,(c,uu____2136)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____2155 = FStar_TypeChecker_NBETerm.unembed e_const c  in
          FStar_Util.bind_opt uu____2155
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2163,(l,uu____2165)::(u,uu____2167)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2190 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              u
             in
          FStar_Util.bind_opt uu____2190
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2200,(t2,uu____2202)::(t1,uu____2204)::(b,uu____2206)::
           (r,uu____2208)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2239 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool r
             in
          FStar_Util.bind_opt uu____2239
            (fun r1  ->
               let uu____2245 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
               FStar_Util.bind_opt uu____2245
                 (fun b1  ->
                    let uu____2251 =
                      FStar_TypeChecker_NBETerm.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2251
                      (fun t11  ->
                         let uu____2257 =
                           FStar_TypeChecker_NBETerm.unembed e_term t2  in
                         FStar_Util.bind_opt uu____2257
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _0_34  ->
                                   FStar_Pervasives_Native.Some _0_34)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2265,(brs,uu____2267)::(t1,uu____2269)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2292 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
          FStar_Util.bind_opt uu____2292
            (fun t2  ->
               let uu____2298 =
                 let uu____2303 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2303 brs  in
               FStar_Util.bind_opt uu____2298
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2321,(tacopt,uu____2323)::(t1,uu____2325)::(e,uu____2327)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2354 = FStar_TypeChecker_NBETerm.unembed e_term e  in
          FStar_Util.bind_opt uu____2354
            (fun e1  ->
               let uu____2360 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____2360
                 (fun t2  ->
                    let uu____2366 =
                      let uu____2371 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2371 tacopt  in
                    FStar_Util.bind_opt uu____2366
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct
          (fv,uu____2389,(tacopt,uu____2391)::(c,uu____2393)::(e,uu____2395)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____2422 = FStar_TypeChecker_NBETerm.unembed e_term e  in
          FStar_Util.bind_opt uu____2422
            (fun e1  ->
               let uu____2428 = FStar_TypeChecker_NBETerm.unembed e_comp c
                  in
               FStar_Util.bind_opt uu____2428
                 (fun c1  ->
                    let uu____2434 =
                      let uu____2439 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2439 tacopt  in
                    FStar_Util.bind_opt uu____2434
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.Construct (fv,uu____2457,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
            FStar_Reflection_Data.Tv_Unknown
      | uu____2474 ->
          ((let uu____2476 =
              let uu____2481 =
                let uu____2482 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____2482
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2481)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2476);
           FStar_Pervasives_Native.None)
       in
    let uu____2483 = mkFV FStar_Reflection_Data.fstar_refl_term_view_fv [] []
       in
    FStar_TypeChecker_NBETerm.mk_emb embed_term_view unembed_term_view
      uu____2483
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view bvv =
    let uu____2506 =
      let uu____2513 =
        let uu____2518 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____2518  in
      let uu____2519 =
        let uu____2526 =
          let uu____2531 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____2531  in
        let uu____2532 =
          let uu____2539 =
            let uu____2544 =
              FStar_TypeChecker_NBETerm.embed e_term
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2544  in
          [uu____2539]  in
        uu____2526 :: uu____2532  in
      uu____2513 :: uu____2519  in
    mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv []
      uu____2506
     in
  let unembed_bv_view t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____2572,(s,uu____2574)::(idx,uu____2576)::(nm,uu____2578)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____2605 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string nm
           in
        FStar_Util.bind_opt uu____2605
          (fun nm1  ->
             let uu____2611 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int idx
                in
             FStar_Util.bind_opt uu____2611
               (fun idx1  ->
                  let uu____2617 = FStar_TypeChecker_NBETerm.unembed e_term s
                     in
                  FStar_Util.bind_opt uu____2617
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____2624 ->
        ((let uu____2626 =
            let uu____2631 =
              let uu____2632 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____2632  in
            (FStar_Errors.Warning_NotEmbedded, uu____2631)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2626);
         FStar_Pervasives_Native.None)
     in
  let uu____2633 = mkFV FStar_Reflection_Data.fstar_refl_bv_view_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_bv_view unembed_bv_view uu____2633 
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____2652 =
          let uu____2659 =
            let uu____2664 = FStar_TypeChecker_NBETerm.embed e_term t  in
            FStar_TypeChecker_NBETerm.as_arg uu____2664  in
          let uu____2665 =
            let uu____2672 =
              let uu____2677 =
                let uu____2678 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____2678 md  in
              FStar_TypeChecker_NBETerm.as_arg uu____2677  in
            [uu____2672]  in
          uu____2659 :: uu____2665  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____2652
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____2702 =
          let uu____2709 =
            let uu____2714 = FStar_TypeChecker_NBETerm.embed e_term pre  in
            FStar_TypeChecker_NBETerm.as_arg uu____2714  in
          let uu____2715 =
            let uu____2722 =
              let uu____2727 = FStar_TypeChecker_NBETerm.embed e_term post1
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2727  in
            [uu____2722]  in
          uu____2709 :: uu____2715  in
        mkConstruct
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____2702
    | FStar_Reflection_Data.C_Unknown  ->
        mkConstruct
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____2755,(md,uu____2757)::(t1,uu____2759)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____2782 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
        FStar_Util.bind_opt uu____2782
          (fun t2  ->
             let uu____2788 =
               let uu____2793 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____2793 md  in
             FStar_Util.bind_opt uu____2788
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____2811,(post,uu____2813)::(pre,uu____2815)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____2838 = FStar_TypeChecker_NBETerm.unembed e_term pre  in
        FStar_Util.bind_opt uu____2838
          (fun pre1  ->
             let uu____2844 = FStar_TypeChecker_NBETerm.unembed e_term post
                in
             FStar_Util.bind_opt uu____2844
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2852,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
          FStar_Reflection_Data.C_Unknown
    | uu____2869 ->
        ((let uu____2871 =
            let uu____2876 =
              let uu____2877 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____2877
               in
            (FStar_Errors.Warning_NotEmbedded, uu____2876)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2871);
         FStar_Pervasives_Native.None)
     in
  let uu____2878 = mkFV FStar_Reflection_Data.fstar_refl_comp_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_comp_view unembed_comp_view
    uu____2878
  
let (e_order : FStar_Order.order FStar_TypeChecker_NBETerm.embedding) =
  let embed_order o =
    match o with
    | FStar_Order.Lt  -> mkConstruct FStar_Reflection_Data.ord_Lt_fv [] []
    | FStar_Order.Eq  -> mkConstruct FStar_Reflection_Data.ord_Eq_fv [] []
    | FStar_Order.Gt  -> mkConstruct FStar_Reflection_Data.ord_Gt_fv [] []
     in
  let unembed_order t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2914,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2930,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____2946,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____2961 ->
        ((let uu____2963 =
            let uu____2968 =
              let uu____2969 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____2969  in
            (FStar_Errors.Warning_NotEmbedded, uu____2968)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2963);
         FStar_Pervasives_Native.None)
     in
  let uu____2970 =
    let uu____2971 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____2971 [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_order unembed_order uu____2970 
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
        let uu____2995 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2995
    | uu____2996 ->
        ((let uu____2998 =
            let uu____3003 =
              let uu____3004 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____3004  in
            (FStar_Errors.Warning_NotEmbedded, uu____3003)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2998);
         FStar_Pervasives_Native.None)
     in
  let uu____3005 = mkFV FStar_Reflection_Data.fstar_refl_sigelt_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt unembed_sigelt uu____3005 
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string
     in
  let embed_ident i =
    let uu____3027 =
      let uu____3032 = FStar_Ident.range_of_id i  in
      let uu____3033 = FStar_Ident.text_of_id i  in (uu____3032, uu____3033)
       in
    FStar_TypeChecker_NBETerm.embed repr uu____3027  in
  let unembed_ident t =
    let uu____3048 = FStar_TypeChecker_NBETerm.unembed repr t  in
    match uu____3048 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____3067 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____3067
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____3072 =
    let uu____3073 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____3074 =
      let uu____3081 =
        let uu____3086 =
          let uu____3087 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          mkFV uu____3087 [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____3086  in
      let uu____3092 =
        let uu____3099 =
          let uu____3104 =
            let uu____3105 =
              FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            mkFV uu____3105 [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____3104  in
        [uu____3099]  in
      uu____3081 :: uu____3092  in
    mkFV uu____3073 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
      uu____3074
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3072 
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
        let uu____3149 =
          let uu____3156 =
            let uu____3161 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3161  in
          let uu____3162 =
            let uu____3169 =
              let uu____3174 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____3174  in
            let uu____3175 =
              let uu____3182 =
                let uu____3187 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____3187  in
              let uu____3190 =
                let uu____3197 =
                  let uu____3202 = FStar_TypeChecker_NBETerm.embed e_term ty
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____3202  in
                let uu____3203 =
                  let uu____3210 =
                    let uu____3215 = FStar_TypeChecker_NBETerm.embed e_term t
                       in
                    FStar_TypeChecker_NBETerm.as_arg uu____3215  in
                  [uu____3210]  in
                uu____3197 :: uu____3203  in
              uu____3182 :: uu____3190  in
            uu____3169 :: uu____3175  in
          uu____3156 :: uu____3162  in
        mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv
          [] uu____3149
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3242 =
          let uu____3249 =
            let uu____3254 = FStar_TypeChecker_NBETerm.embed e_string_list nm
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3254  in
          let uu____3257 =
            let uu____3264 =
              let uu____3269 = FStar_TypeChecker_NBETerm.embed e_term ty  in
              FStar_TypeChecker_NBETerm.as_arg uu____3269  in
            [uu____3264]  in
          uu____3249 :: uu____3257  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____3242
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____3299 =
          let uu____3306 =
            let uu____3311 = FStar_TypeChecker_NBETerm.embed e_string_list nm
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3311  in
          let uu____3314 =
            let uu____3321 =
              let uu____3326 =
                FStar_TypeChecker_NBETerm.embed e_univ_names univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3326  in
            let uu____3329 =
              let uu____3336 =
                let uu____3341 = FStar_TypeChecker_NBETerm.embed e_binders bs
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____3341  in
              let uu____3342 =
                let uu____3349 =
                  let uu____3354 = FStar_TypeChecker_NBETerm.embed e_term t
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____3354  in
                let uu____3355 =
                  let uu____3362 =
                    let uu____3367 =
                      let uu____3368 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____3368 dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____3367  in
                  [uu____3362]  in
                uu____3349 :: uu____3355  in
              uu____3336 :: uu____3342  in
            uu____3321 :: uu____3329  in
          uu____3306 :: uu____3314  in
        mkConstruct
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____3299
    | FStar_Reflection_Data.Unk  ->
        mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv []
          []
     in
  let unembed_sigelt_view t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3420,(dcs,uu____3422)::(t1,uu____3424)::(bs,uu____3426)::
         (us,uu____3428)::(nm,uu____3430)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____3465 = FStar_TypeChecker_NBETerm.unembed e_string_list nm
           in
        FStar_Util.bind_opt uu____3465
          (fun nm1  ->
             let uu____3479 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names us  in
             FStar_Util.bind_opt uu____3479
               (fun us1  ->
                  let uu____3493 =
                    FStar_TypeChecker_NBETerm.unembed e_binders bs  in
                  FStar_Util.bind_opt uu____3493
                    (fun bs1  ->
                       let uu____3499 =
                         FStar_TypeChecker_NBETerm.unembed e_term t1  in
                       FStar_Util.bind_opt uu____3499
                         (fun t2  ->
                            let uu____3505 =
                              let uu____3512 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____3512
                                dcs
                               in
                            FStar_Util.bind_opt uu____3505
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3544,(t1,uu____3546)::(ty,uu____3548)::(univs1,uu____3550)::
         (fvar1,uu____3552)::(r,uu____3554)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____3589 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            r
           in
        FStar_Util.bind_opt uu____3589
          (fun r1  ->
             let uu____3595 = FStar_TypeChecker_NBETerm.unembed e_fv fvar1
                in
             FStar_Util.bind_opt uu____3595
               (fun fvar2  ->
                  let uu____3601 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names univs1  in
                  FStar_Util.bind_opt uu____3601
                    (fun univs2  ->
                       let uu____3615 =
                         FStar_TypeChecker_NBETerm.unembed e_term ty  in
                       FStar_Util.bind_opt uu____3615
                         (fun ty1  ->
                            let uu____3621 =
                              FStar_TypeChecker_NBETerm.unembed e_term t1  in
                            FStar_Util.bind_opt uu____3621
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _0_44  ->
                                      FStar_Pervasives_Native.Some _0_44)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3631,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____3646 ->
        ((let uu____3648 =
            let uu____3653 =
              let uu____3654 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____3654
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3653)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3648);
         FStar_Pervasives_Native.None)
     in
  let uu____3655 = mkFV FStar_Reflection_Data.fstar_refl_sigelt_view_fv [] []
     in
  FStar_TypeChecker_NBETerm.mk_emb embed_sigelt_view unembed_sigelt_view
    uu____3655
  
let (e_exp : FStar_Reflection_Data.exp FStar_TypeChecker_NBETerm.embedding) =
  let rec embed_exp e =
    match e with
    | FStar_Reflection_Data.Unit  ->
        mkConstruct FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.fv
          [] []
    | FStar_Reflection_Data.Var i ->
        let uu____3673 =
          let uu____3680 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____3680]  in
        mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv
          [] uu____3673
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____3695 =
          let uu____3702 =
            let uu____3707 = embed_exp e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____3707  in
          let uu____3708 =
            let uu____3715 =
              let uu____3720 = embed_exp e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____3720  in
            [uu____3715]  in
          uu____3702 :: uu____3708  in
        mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv
          [] uu____3695
     in
  let rec unembed_exp t =
    match t with
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3744,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.Construct (fv,uu____3760,(i,uu____3762)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____3781 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int i
           in
        FStar_Util.bind_opt uu____3781
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.Construct
        (fv,uu____3789,(e2,uu____3791)::(e1,uu____3793)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____3816 = unembed_exp e1  in
        FStar_Util.bind_opt uu____3816
          (fun e11  ->
             let uu____3822 = unembed_exp e2  in
             FStar_Util.bind_opt uu____3822
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____3829 ->
        ((let uu____3831 =
            let uu____3836 =
              let uu____3837 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____3837  in
            (FStar_Errors.Warning_NotEmbedded, uu____3836)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3831);
         FStar_Pervasives_Native.None)
     in
  let uu____3838 = mkFV FStar_Reflection_Data.fstar_refl_exp_fv [] []  in
  FStar_TypeChecker_NBETerm.mk_emb embed_exp unembed_exp uu____3838 
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_bv e_aqualv 
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding) = e_term 
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_attribute 