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
  
let mk_emb :
  'Auu____39 .
    ('Auu____39 -> FStar_TypeChecker_NBETerm.t) ->
      (FStar_TypeChecker_NBETerm.t ->
         'Auu____39 FStar_Pervasives_Native.option)
        ->
        FStar_TypeChecker_NBETerm.t ->
          'Auu____39 FStar_TypeChecker_NBETerm.embedding
  =
  fun em  ->
    fun un  ->
      fun typ  ->
        {
          FStar_TypeChecker_NBETerm.em = em;
          FStar_TypeChecker_NBETerm.un = un;
          FStar_TypeChecker_NBETerm.typ = typ
        }
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv bv =
    mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv
     in
  let unembed_bv t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy li when
        li.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____90 = FStar_Dyn.undyn li.FStar_Syntax_Syntax.blob  in
        FStar_All.pipe_left
          (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____90
    | uu____93 ->
        ((let uu____95 =
            let uu____100 =
              let uu____101 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____101  in
            (FStar_Errors.Warning_NotEmbedded, uu____100)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____95);
         FStar_Pervasives_Native.None)
     in
  let uu____102 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_bv_fv []
      []
     in
  mk_emb embed_bv unembed_bv uu____102 
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
        let uu____126 = FStar_Dyn.undyn li.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____126
    | uu____127 ->
        ((let uu____129 =
            let uu____134 =
              let uu____135 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____135  in
            (FStar_Errors.Warning_NotEmbedded, uu____134)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____129);
         FStar_Pervasives_Native.None)
     in
  let uu____136 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_binder_fv
      [] []
     in
  mk_emb embed_binder unembed_binder uu____136 
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
          let uu____186 = f x  in
          FStar_Util.bind_opt uu____186
            (fun x1  ->
               let uu____194 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____194
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
      | uu____257 -> FStar_Pervasives_Native.None  in
    let uu____258 =
      FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_term_fv
        [] []
       in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ = uu____258
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
        let uu____290 =
          let uu____291 =
            let uu____296 = FStar_TypeChecker_NBETerm.embed e_term t  in
            FStar_TypeChecker_NBETerm.as_arg uu____296  in
          [uu____291]  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv []
          uu____290
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
    | FStar_TypeChecker_NBETerm.FV (fv,[],(t1,uu____343)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
        ->
        let uu____360 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
        FStar_Util.bind_opt uu____360
          (fun t2  ->
             FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta t2))
    | uu____365 ->
        ((let uu____367 =
            let uu____372 =
              let uu____373 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded aqualv: %s" uu____373  in
            (FStar_Errors.Warning_NotEmbedded, uu____372)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____367);
         FStar_Pervasives_Native.None)
     in
  let uu____374 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_aqualv_fv
      [] []
     in
  mk_emb embed_aqualv unembed_aqualv uu____374 
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
        let uu____400 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____400
    | uu____401 ->
        ((let uu____403 =
            let uu____408 =
              let uu____409 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____409  in
            (FStar_Errors.Warning_NotEmbedded, uu____408)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____403);
         FStar_Pervasives_Native.None)
     in
  let uu____410 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_fv_fv []
      []
     in
  mk_emb embed_fv unembed_fv uu____410 
let (e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp c =
    mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp
     in
  let unembed_comp t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____434 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____434
    | uu____435 ->
        ((let uu____437 =
            let uu____442 =
              let uu____443 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____443  in
            (FStar_Errors.Warning_NotEmbedded, uu____442)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____437);
         FStar_Pervasives_Native.None)
     in
  let uu____444 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_comp_fv
      [] []
     in
  mk_emb embed_comp unembed_comp uu____444 
let (e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding) =
  let embed_env e =
    mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env
     in
  let unembed_env t =
    match t with
    | FStar_TypeChecker_NBETerm.Lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____468 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____468
    | uu____469 ->
        ((let uu____471 =
            let uu____476 =
              let uu____477 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____477  in
            (FStar_Errors.Warning_NotEmbedded, uu____476)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____471);
         FStar_Pervasives_Native.None)
     in
  let uu____478 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_env_fv []
      []
     in
  mk_emb embed_env unembed_env uu____478 
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
        let uu____504 =
          let uu____505 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____505]  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv []
          uu____504
    | FStar_Reflection_Data.C_String s ->
        let uu____519 =
          let uu____520 =
            let uu____525 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_string s
               in
            FStar_TypeChecker_NBETerm.as_arg uu____525  in
          [uu____520]  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv []
          uu____519
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
    | FStar_TypeChecker_NBETerm.FV (fv,[],(i,uu____585)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
        ->
        let uu____602 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int i
           in
        FStar_Util.bind_opt uu____602
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Reflection_Data.C_Int i1))
    | FStar_TypeChecker_NBETerm.FV (fv,[],(s,uu____611)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
        ->
        let uu____628 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string s
           in
        FStar_Util.bind_opt uu____628
          (fun s1  ->
             FStar_All.pipe_left
               (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
               (FStar_Reflection_Data.C_String s1))
    | uu____635 ->
        ((let uu____637 =
            let uu____642 =
              let uu____643 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded vconst: %s" uu____643  in
            (FStar_Errors.Warning_NotEmbedded, uu____642)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____637);
         FStar_Pervasives_Native.None)
     in
  let uu____644 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_vconst_fv
      [] []
     in
  mk_emb embed_const unembed_const uu____644 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding)
  =
  fun uu____655  ->
    let rec embed_pattern p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____663 =
            let uu____664 =
              let uu____669 = FStar_TypeChecker_NBETerm.embed e_const c  in
              FStar_TypeChecker_NBETerm.as_arg uu____669  in
            [uu____664]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv
            [] uu____663
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____684 =
            let uu____685 =
              let uu____690 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____690  in
            let uu____691 =
              let uu____698 =
                let uu____703 =
                  let uu____704 =
                    let uu____709 = e_pattern' ()  in
                    FStar_TypeChecker_NBETerm.e_list uu____709  in
                  FStar_TypeChecker_NBETerm.embed uu____704 ps  in
                FStar_TypeChecker_NBETerm.as_arg uu____703  in
              [uu____698]  in
            uu____685 :: uu____691  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv []
            uu____684
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____727 =
            let uu____728 =
              let uu____733 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____733  in
            [uu____728]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv []
            uu____727
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____743 =
            let uu____744 =
              let uu____749 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____749  in
            [uu____744]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv []
            uu____743
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____760 =
            let uu____761 =
              let uu____766 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____766  in
            let uu____767 =
              let uu____774 =
                let uu____779 = FStar_TypeChecker_NBETerm.embed e_term t  in
                FStar_TypeChecker_NBETerm.as_arg uu____779  in
              [uu____774]  in
            uu____761 :: uu____767  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv
            [] uu____760
       in
    let rec unembed_pattern t =
      match t with
      | FStar_TypeChecker_NBETerm.FV (fv,[],(c,uu____804)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
          ->
          let uu____821 = FStar_TypeChecker_NBETerm.unembed e_const c  in
          FStar_Util.bind_opt uu____821
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                 (FStar_Reflection_Data.Pat_Constant c1))
      | FStar_TypeChecker_NBETerm.FV
          (fv,[],(f,uu____830)::(ps,uu____832)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
          ->
          let uu____853 = FStar_TypeChecker_NBETerm.unembed e_fv f  in
          FStar_Util.bind_opt uu____853
            (fun f1  ->
               let uu____859 =
                 let uu____864 =
                   let uu____869 = e_pattern' ()  in
                   FStar_TypeChecker_NBETerm.e_list uu____869  in
                 FStar_TypeChecker_NBETerm.unembed uu____864 ps  in
               FStar_Util.bind_opt uu____859
                 (fun ps1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
      | FStar_TypeChecker_NBETerm.FV (fv,[],(bv,uu____886)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
          ->
          let uu____903 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____903
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                 (FStar_Reflection_Data.Pat_Var bv1))
      | FStar_TypeChecker_NBETerm.FV (fv,[],(bv,uu____912)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
          ->
          let uu____929 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____929
            (fun bv1  ->
               FStar_All.pipe_left
                 (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                 (FStar_Reflection_Data.Pat_Wild bv1))
      | FStar_TypeChecker_NBETerm.FV
          (fv,[],(bv,uu____938)::(t1,uu____940)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
          ->
          let uu____961 = FStar_TypeChecker_NBETerm.unembed e_bv bv  in
          FStar_Util.bind_opt uu____961
            (fun bv1  ->
               let uu____967 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____967
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Pat_Dot_Term (bv1, t2))))
      | uu____974 ->
          ((let uu____976 =
              let uu____981 =
                let uu____982 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded pattern: %s" uu____982
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____981)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____976);
           FStar_Pervasives_Native.None)
       in
    let uu____983 =
      FStar_TypeChecker_NBETerm.mkFV
        FStar_Reflection_Data.fstar_refl_pattern_fv [] []
       in
    mk_emb embed_pattern unembed_pattern uu____983
  
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
    let uu____1025 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1025
  
let (e_argv_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let uu____1059 = e_term_aq aq  in
    FStar_TypeChecker_NBETerm.e_tuple2 uu____1059 e_aqualv
  
let rec unlazy_as_t :
  'Auu____1068 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_TypeChecker_NBETerm.t -> 'Auu____1068
  =
  fun k  ->
    fun t  ->
      match t with
      | FStar_TypeChecker_NBETerm.Lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.typ = uu____1081;
            FStar_Syntax_Syntax.rng = uu____1082;_}
          when k = k' -> FStar_Dyn.undyn v1
      | uu____1085 -> failwith "Not a Lazy of the expected kind (NBE)"
  
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
          let uu____1120 =
            let uu____1121 =
              let uu____1126 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1126  in
            [uu____1121]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1120
      | FStar_Reflection_Data.Tv_BVar bv ->
          let uu____1136 =
            let uu____1137 =
              let uu____1142 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1142  in
            [uu____1137]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv []
            uu____1136
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1152 =
            let uu____1153 =
              let uu____1158 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1158  in
            [uu____1153]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv []
            uu____1152
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1169 =
            let uu____1170 =
              let uu____1175 =
                let uu____1176 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1176 hd1  in
              FStar_TypeChecker_NBETerm.as_arg uu____1175  in
            let uu____1179 =
              let uu____1186 =
                let uu____1191 =
                  let uu____1192 = e_argv_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1192 a  in
                FStar_TypeChecker_NBETerm.as_arg uu____1191  in
              [uu____1186]  in
            uu____1170 :: uu____1179  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv []
            uu____1169
      | FStar_Reflection_Data.Tv_Abs (b,t) ->
          let uu____1217 =
            let uu____1218 =
              let uu____1223 = FStar_TypeChecker_NBETerm.embed e_binder b  in
              FStar_TypeChecker_NBETerm.as_arg uu____1223  in
            let uu____1224 =
              let uu____1231 =
                let uu____1236 =
                  let uu____1237 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1237 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1236  in
              [uu____1231]  in
            uu____1218 :: uu____1224  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv []
            uu____1217
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1254 =
            let uu____1255 =
              let uu____1260 = FStar_TypeChecker_NBETerm.embed e_binder b  in
              FStar_TypeChecker_NBETerm.as_arg uu____1260  in
            let uu____1261 =
              let uu____1268 =
                let uu____1273 = FStar_TypeChecker_NBETerm.embed e_comp c  in
                FStar_TypeChecker_NBETerm.as_arg uu____1273  in
              [uu____1268]  in
            uu____1255 :: uu____1261  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv []
            uu____1254
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1287 =
            let uu____1288 =
              let uu____1293 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_unit ()
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1293  in
            [uu____1288]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv []
            uu____1287
      | FStar_Reflection_Data.Tv_Refine (bv,t) ->
          let uu____1304 =
            let uu____1305 =
              let uu____1310 = FStar_TypeChecker_NBETerm.embed e_bv bv  in
              FStar_TypeChecker_NBETerm.as_arg uu____1310  in
            let uu____1311 =
              let uu____1318 =
                let uu____1323 =
                  let uu____1324 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1324 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1323  in
              [uu____1318]  in
            uu____1305 :: uu____1311  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv []
            uu____1304
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1340 =
            let uu____1341 =
              let uu____1346 = FStar_TypeChecker_NBETerm.embed e_const c  in
              FStar_TypeChecker_NBETerm.as_arg uu____1346  in
            [uu____1341]  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv []
            uu____1340
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____1357 =
            let uu____1358 =
              let uu____1363 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_int u
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1363  in
            let uu____1364 =
              let uu____1371 =
                let uu____1376 =
                  mk_lazy (u, d) FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____1376  in
              [uu____1371]  in
            uu____1358 :: uu____1364  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv []
            uu____1357
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1397 =
            let uu____1398 =
              let uu____1403 =
                FStar_TypeChecker_NBETerm.embed
                  FStar_TypeChecker_NBETerm.e_bool r
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____1403  in
            let uu____1404 =
              let uu____1411 =
                let uu____1416 = FStar_TypeChecker_NBETerm.embed e_bv b  in
                FStar_TypeChecker_NBETerm.as_arg uu____1416  in
              let uu____1417 =
                let uu____1424 =
                  let uu____1429 =
                    let uu____1430 = e_term_aq aq  in
                    FStar_TypeChecker_NBETerm.embed uu____1430 t1  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1429  in
                let uu____1433 =
                  let uu____1440 =
                    let uu____1445 =
                      let uu____1446 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.embed uu____1446 t2  in
                    FStar_TypeChecker_NBETerm.as_arg uu____1445  in
                  [uu____1440]  in
                uu____1424 :: uu____1433  in
              uu____1411 :: uu____1417  in
            uu____1398 :: uu____1404  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv []
            uu____1397
      | FStar_Reflection_Data.Tv_Match (t,brs) ->
          let uu____1475 =
            let uu____1476 =
              let uu____1481 =
                let uu____1482 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1482 t  in
              FStar_TypeChecker_NBETerm.as_arg uu____1481  in
            let uu____1485 =
              let uu____1492 =
                let uu____1497 =
                  let uu____1498 =
                    let uu____1507 = e_branch_aq aq  in
                    FStar_TypeChecker_NBETerm.e_list uu____1507  in
                  FStar_TypeChecker_NBETerm.embed uu____1498 brs  in
                FStar_TypeChecker_NBETerm.as_arg uu____1497  in
              [uu____1492]  in
            uu____1476 :: uu____1485  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv []
            uu____1475
      | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
          let uu____1543 =
            let uu____1544 =
              let uu____1549 =
                let uu____1550 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1550 e  in
              FStar_TypeChecker_NBETerm.as_arg uu____1549  in
            let uu____1553 =
              let uu____1560 =
                let uu____1565 =
                  let uu____1566 = e_term_aq aq  in
                  FStar_TypeChecker_NBETerm.embed uu____1566 t  in
                FStar_TypeChecker_NBETerm.as_arg uu____1565  in
              let uu____1569 =
                let uu____1576 =
                  let uu____1581 =
                    let uu____1582 =
                      let uu____1587 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____1587  in
                    FStar_TypeChecker_NBETerm.embed uu____1582 tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1581  in
                [uu____1576]  in
              uu____1560 :: uu____1569  in
            uu____1544 :: uu____1553  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____1543
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____1615 =
            let uu____1616 =
              let uu____1621 =
                let uu____1622 = e_term_aq aq  in
                FStar_TypeChecker_NBETerm.embed uu____1622 e  in
              FStar_TypeChecker_NBETerm.as_arg uu____1621  in
            let uu____1625 =
              let uu____1632 =
                let uu____1637 = FStar_TypeChecker_NBETerm.embed e_comp c  in
                FStar_TypeChecker_NBETerm.as_arg uu____1637  in
              let uu____1638 =
                let uu____1645 =
                  let uu____1650 =
                    let uu____1651 =
                      let uu____1656 = e_term_aq aq  in
                      FStar_TypeChecker_NBETerm.e_option uu____1656  in
                    FStar_TypeChecker_NBETerm.embed uu____1651 tacopt  in
                  FStar_TypeChecker_NBETerm.as_arg uu____1650  in
                [uu____1645]  in
              uu____1632 :: uu____1638  in
            uu____1616 :: uu____1625  in
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv []
            uu____1615
      | FStar_Reflection_Data.Tv_Unknown  ->
          FStar_TypeChecker_NBETerm.mkFV
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv []
            []
       in
    let unembed_term_view t =
      match t with
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1692,(b,uu____1694)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
          ->
          let uu____1713 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1713
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                 (FStar_Reflection_Data.Tv_Var b1))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1721,(b,uu____1723)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
          ->
          let uu____1742 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1742
            (fun b1  ->
               FStar_All.pipe_left
                 (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                 (FStar_Reflection_Data.Tv_BVar b1))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1750,(f,uu____1752)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
          ->
          let uu____1771 = FStar_TypeChecker_NBETerm.unembed e_fv f  in
          FStar_Util.bind_opt uu____1771
            (fun f1  ->
               FStar_All.pipe_left
                 (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                 (FStar_Reflection_Data.Tv_FVar f1))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1779,(l,uu____1781)::(r,uu____1783)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
          ->
          let uu____1806 = FStar_TypeChecker_NBETerm.unembed e_term l  in
          FStar_Util.bind_opt uu____1806
            (fun l1  ->
               let uu____1812 = FStar_TypeChecker_NBETerm.unembed e_argv r
                  in
               FStar_Util.bind_opt uu____1812
                 (fun r1  ->
                    FStar_All.pipe_left
                      (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                      (FStar_Reflection_Data.Tv_App (l1, r1))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1820,(b,uu____1822)::(t1,uu____1824)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
          ->
          let uu____1847 = FStar_TypeChecker_NBETerm.unembed e_binder b  in
          FStar_Util.bind_opt uu____1847
            (fun b1  ->
               let uu____1853 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____1853
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                      (FStar_Reflection_Data.Tv_Abs (b1, t2))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1861,(b,uu____1863)::(t1,uu____1865)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
          ->
          let uu____1888 = FStar_TypeChecker_NBETerm.unembed e_binder b  in
          FStar_Util.bind_opt uu____1888
            (fun b1  ->
               let uu____1894 = FStar_TypeChecker_NBETerm.unembed e_comp t1
                  in
               FStar_Util.bind_opt uu____1894
                 (fun c  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Arrow (b1, c))))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1902,(u,uu____1904)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
          ->
          let uu____1923 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_unit u
             in
          FStar_Util.bind_opt uu____1923
            (fun u1  ->
               FStar_All.pipe_left
                 (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                 (FStar_Reflection_Data.Tv_Type ()))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____1931,(b,uu____1933)::(t1,uu____1935)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
          ->
          let uu____1958 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
          FStar_Util.bind_opt uu____1958
            (fun b1  ->
               let uu____1964 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____1964
                 (fun t2  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Refine (b1, t2))))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____1972,(c,uu____1974)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
          ->
          let uu____1993 = FStar_TypeChecker_NBETerm.unembed e_const c  in
          FStar_Util.bind_opt uu____1993
            (fun c1  ->
               FStar_All.pipe_left
                 (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                 (FStar_Reflection_Data.Tv_Const c1))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____2001,(u,uu____2003)::(l,uu____2005)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
          ->
          let uu____2028 =
            FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int
              u
             in
          FStar_Util.bind_opt uu____2028
            (fun u1  ->
               let ctx_u_s = unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l  in
               FStar_All.pipe_left
                 (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                 (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____2038,(r,uu____2040)::(b,uu____2042)::(t1,uu____2044)::
           (t2,uu____2046)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
          ->
          let uu____2077 =
            FStar_TypeChecker_NBETerm.unembed
              FStar_TypeChecker_NBETerm.e_bool r
             in
          FStar_Util.bind_opt uu____2077
            (fun r1  ->
               let uu____2083 = FStar_TypeChecker_NBETerm.unembed e_bv b  in
               FStar_Util.bind_opt uu____2083
                 (fun b1  ->
                    let uu____2089 =
                      FStar_TypeChecker_NBETerm.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2089
                      (fun t11  ->
                         let uu____2095 =
                           FStar_TypeChecker_NBETerm.unembed e_term t2  in
                         FStar_Util.bind_opt uu____2095
                           (fun t21  ->
                              FStar_All.pipe_left
                                (fun _0_34  ->
                                   FStar_Pervasives_Native.Some _0_34)
                                (FStar_Reflection_Data.Tv_Let
                                   (r1, b1, t11, t21))))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____2103,(t1,uu____2105)::(brs,uu____2107)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
          ->
          let uu____2130 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
          FStar_Util.bind_opt uu____2130
            (fun t2  ->
               let uu____2136 =
                 let uu____2141 = FStar_TypeChecker_NBETerm.e_list e_branch
                    in
                 FStar_TypeChecker_NBETerm.unembed uu____2141 brs  in
               FStar_Util.bind_opt uu____2136
                 (fun brs1  ->
                    FStar_All.pipe_left
                      (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                      (FStar_Reflection_Data.Tv_Match (t2, brs1))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____2159,(e,uu____2161)::(t1,uu____2163)::(tacopt,uu____2165)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
          ->
          let uu____2192 = FStar_TypeChecker_NBETerm.unembed e_term e  in
          FStar_Util.bind_opt uu____2192
            (fun e1  ->
               let uu____2198 = FStar_TypeChecker_NBETerm.unembed e_term t1
                  in
               FStar_Util.bind_opt uu____2198
                 (fun t2  ->
                    let uu____2204 =
                      let uu____2209 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2209 tacopt  in
                    FStar_Util.bind_opt uu____2204
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_36  -> FStar_Pervasives_Native.Some _0_36)
                           (FStar_Reflection_Data.Tv_AscribedT
                              (e1, t2, tacopt1)))))
      | FStar_TypeChecker_NBETerm.FV
          (fv,uu____2227,(e,uu____2229)::(c,uu____2231)::(tacopt,uu____2233)::[])
          when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
          ->
          let uu____2260 = FStar_TypeChecker_NBETerm.unembed e_term e  in
          FStar_Util.bind_opt uu____2260
            (fun e1  ->
               let uu____2266 = FStar_TypeChecker_NBETerm.unembed e_comp c
                  in
               FStar_Util.bind_opt uu____2266
                 (fun c1  ->
                    let uu____2272 =
                      let uu____2277 =
                        FStar_TypeChecker_NBETerm.e_option e_term  in
                      FStar_TypeChecker_NBETerm.unembed uu____2277 tacopt  in
                    FStar_Util.bind_opt uu____2272
                      (fun tacopt1  ->
                         FStar_All.pipe_left
                           (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                           (FStar_Reflection_Data.Tv_AscribedC
                              (e1, c1, tacopt1)))))
      | FStar_TypeChecker_NBETerm.FV (fv,uu____2295,[]) when
          FStar_Syntax_Syntax.fv_eq_lid fv
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
          ->
          FStar_All.pipe_left
            (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
            FStar_Reflection_Data.Tv_Unknown
      | uu____2312 ->
          ((let uu____2314 =
              let uu____2319 =
                let uu____2320 = FStar_TypeChecker_NBETerm.t_to_string t  in
                FStar_Util.format1 "Not an embedded term_view: %s" uu____2320
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____2319)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____2314);
           FStar_Pervasives_Native.None)
       in
    let uu____2321 =
      FStar_TypeChecker_NBETerm.mkFV
        FStar_Reflection_Data.fstar_refl_term_view_fv [] []
       in
    mk_emb embed_term_view unembed_term_view uu____2321
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_bv_view bvv =
    let uu____2344 =
      let uu____2345 =
        let uu____2350 =
          FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
            bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_TypeChecker_NBETerm.as_arg uu____2350  in
      let uu____2351 =
        let uu____2358 =
          let uu____2363 =
            FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
              bvv.FStar_Reflection_Data.bv_index
             in
          FStar_TypeChecker_NBETerm.as_arg uu____2363  in
        let uu____2364 =
          let uu____2371 =
            let uu____2376 =
              FStar_TypeChecker_NBETerm.embed e_term
                bvv.FStar_Reflection_Data.bv_sort
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2376  in
          [uu____2371]  in
        uu____2358 :: uu____2364  in
      uu____2345 :: uu____2351  in
    FStar_TypeChecker_NBETerm.mkFV
      FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv [] uu____2344
     in
  let unembed_bv_view t =
    match t with
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____2404,(nm,uu____2406)::(idx,uu____2408)::(s,uu____2410)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
        ->
        let uu____2437 =
          FStar_TypeChecker_NBETerm.unembed
            FStar_TypeChecker_NBETerm.e_string nm
           in
        FStar_Util.bind_opt uu____2437
          (fun nm1  ->
             let uu____2443 =
               FStar_TypeChecker_NBETerm.unembed
                 FStar_TypeChecker_NBETerm.e_int idx
                in
             FStar_Util.bind_opt uu____2443
               (fun idx1  ->
                  let uu____2449 = FStar_TypeChecker_NBETerm.unembed e_term s
                     in
                  FStar_Util.bind_opt uu____2449
                    (fun s1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         {
                           FStar_Reflection_Data.bv_ppname = nm1;
                           FStar_Reflection_Data.bv_index = idx1;
                           FStar_Reflection_Data.bv_sort = s1
                         })))
    | uu____2456 ->
        ((let uu____2458 =
            let uu____2463 =
              let uu____2464 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded bv_view: %s" uu____2464  in
            (FStar_Errors.Warning_NotEmbedded, uu____2463)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2458);
         FStar_Pervasives_Native.None)
     in
  let uu____2465 =
    FStar_TypeChecker_NBETerm.mkFV
      FStar_Reflection_Data.fstar_refl_bv_view_fv [] []
     in
  mk_emb embed_bv_view unembed_bv_view uu____2465 
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____2484 =
          let uu____2485 =
            let uu____2490 = FStar_TypeChecker_NBETerm.embed e_term t  in
            FStar_TypeChecker_NBETerm.as_arg uu____2490  in
          let uu____2491 =
            let uu____2498 =
              let uu____2503 =
                let uu____2504 = FStar_TypeChecker_NBETerm.e_option e_term
                   in
                FStar_TypeChecker_NBETerm.embed uu____2504 md  in
              FStar_TypeChecker_NBETerm.as_arg uu____2503  in
            [uu____2498]  in
          uu____2485 :: uu____2491  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv []
          uu____2484
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____2528 =
          let uu____2529 =
            let uu____2534 = FStar_TypeChecker_NBETerm.embed e_term pre  in
            FStar_TypeChecker_NBETerm.as_arg uu____2534  in
          let uu____2535 =
            let uu____2542 =
              let uu____2547 = FStar_TypeChecker_NBETerm.embed e_term post1
                 in
              FStar_TypeChecker_NBETerm.as_arg uu____2547  in
            [uu____2542]  in
          uu____2529 :: uu____2535  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv []
          uu____2528
    | FStar_Reflection_Data.C_Unknown  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] []
     in
  let unembed_comp_view t =
    match t with
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____2575,(t1,uu____2577)::(md,uu____2579)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
        ->
        let uu____2602 = FStar_TypeChecker_NBETerm.unembed e_term t1  in
        FStar_Util.bind_opt uu____2602
          (fun t2  ->
             let uu____2608 =
               let uu____2613 = FStar_TypeChecker_NBETerm.e_option e_term  in
               FStar_TypeChecker_NBETerm.unembed uu____2613 md  in
             FStar_Util.bind_opt uu____2608
               (fun md1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Total (t2, md1))))
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____2631,(pre,uu____2633)::(post,uu____2635)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
        ->
        let uu____2658 = FStar_TypeChecker_NBETerm.unembed e_term pre  in
        FStar_Util.bind_opt uu____2658
          (fun pre1  ->
             let uu____2664 = FStar_TypeChecker_NBETerm.unembed e_term post
                in
             FStar_Util.bind_opt uu____2664
               (fun post1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_Lemma (pre1, post1))))
    | FStar_TypeChecker_NBETerm.FV (fv,uu____2672,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
        ->
        FStar_All.pipe_left
          (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
          FStar_Reflection_Data.C_Unknown
    | uu____2689 ->
        ((let uu____2691 =
            let uu____2696 =
              let uu____2697 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded comp_view: %s" uu____2697
               in
            (FStar_Errors.Warning_NotEmbedded, uu____2696)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2691);
         FStar_Pervasives_Native.None)
     in
  let uu____2698 =
    FStar_TypeChecker_NBETerm.mkFV
      FStar_Reflection_Data.fstar_refl_comp_view_fv [] []
     in
  mk_emb embed_comp_view unembed_comp_view uu____2698 
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
    | FStar_TypeChecker_NBETerm.FV (fv,uu____2734,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | FStar_TypeChecker_NBETerm.FV (fv,uu____2750,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | FStar_TypeChecker_NBETerm.FV (fv,uu____2766,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu____2781 ->
        ((let uu____2783 =
            let uu____2788 =
              let uu____2789 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded order: %s" uu____2789  in
            (FStar_Errors.Warning_NotEmbedded, uu____2788)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2783);
         FStar_Pervasives_Native.None)
     in
  let uu____2790 =
    let uu____2791 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_TypeChecker_NBETerm.mkFV uu____2791 [] []  in
  mk_emb embed_order unembed_order uu____2790 
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
        let uu____2815 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2815
    | uu____2816 ->
        ((let uu____2818 =
            let uu____2823 =
              let uu____2824 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____2824  in
            (FStar_Errors.Warning_NotEmbedded, uu____2823)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____2818);
         FStar_Pervasives_Native.None)
     in
  let uu____2825 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_sigelt_fv
      [] []
     in
  mk_emb embed_sigelt unembed_sigelt uu____2825 
let (e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding) =
  let repr =
    FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range
      FStar_TypeChecker_NBETerm.e_string
     in
  let embed_ident i =
    let uu____2847 =
      let uu____2852 = FStar_Ident.range_of_id i  in
      let uu____2853 = FStar_Ident.text_of_id i  in (uu____2852, uu____2853)
       in
    FStar_TypeChecker_NBETerm.embed repr uu____2847  in
  let unembed_ident t =
    let uu____2868 = FStar_TypeChecker_NBETerm.unembed repr t  in
    match uu____2868 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____2887 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____2887
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____2892 =
    let uu____2893 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    let uu____2894 =
      let uu____2895 =
        let uu____2900 =
          let uu____2901 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_TypeChecker_NBETerm.mkFV uu____2901 [] []  in
        FStar_TypeChecker_NBETerm.as_arg uu____2900  in
      let uu____2906 =
        let uu____2913 =
          let uu____2918 =
            let uu____2919 =
              FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            FStar_TypeChecker_NBETerm.mkFV uu____2919 [] []  in
          FStar_TypeChecker_NBETerm.as_arg uu____2918  in
        [uu____2913]  in
      uu____2895 :: uu____2906  in
    FStar_TypeChecker_NBETerm.mkFV uu____2893
      [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2894
     in
  mk_emb embed_ident unembed_ident uu____2892 
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
        let uu____2963 =
          let uu____2964 =
            let uu____2969 =
              FStar_TypeChecker_NBETerm.embed
                FStar_TypeChecker_NBETerm.e_bool r
               in
            FStar_TypeChecker_NBETerm.as_arg uu____2969  in
          let uu____2970 =
            let uu____2977 =
              let uu____2982 = FStar_TypeChecker_NBETerm.embed e_fv fv  in
              FStar_TypeChecker_NBETerm.as_arg uu____2982  in
            let uu____2983 =
              let uu____2990 =
                let uu____2995 =
                  FStar_TypeChecker_NBETerm.embed e_univ_names univs1  in
                FStar_TypeChecker_NBETerm.as_arg uu____2995  in
              let uu____2998 =
                let uu____3005 =
                  let uu____3010 = FStar_TypeChecker_NBETerm.embed e_term ty
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____3010  in
                let uu____3011 =
                  let uu____3018 =
                    let uu____3023 = FStar_TypeChecker_NBETerm.embed e_term t
                       in
                    FStar_TypeChecker_NBETerm.as_arg uu____3023  in
                  [uu____3018]  in
                uu____3005 :: uu____3011  in
              uu____2990 :: uu____2998  in
            uu____2977 :: uu____2983  in
          uu____2964 :: uu____2970  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv []
          uu____2963
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3050 =
          let uu____3051 =
            let uu____3056 = FStar_TypeChecker_NBETerm.embed e_string_list nm
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3056  in
          let uu____3059 =
            let uu____3066 =
              let uu____3071 = FStar_TypeChecker_NBETerm.embed e_term ty  in
              FStar_TypeChecker_NBETerm.as_arg uu____3071  in
            [uu____3066]  in
          uu____3051 :: uu____3059  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv
          [] uu____3050
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____3101 =
          let uu____3102 =
            let uu____3107 = FStar_TypeChecker_NBETerm.embed e_string_list nm
               in
            FStar_TypeChecker_NBETerm.as_arg uu____3107  in
          let uu____3110 =
            let uu____3117 =
              let uu____3122 =
                FStar_TypeChecker_NBETerm.embed e_univ_names univs1  in
              FStar_TypeChecker_NBETerm.as_arg uu____3122  in
            let uu____3125 =
              let uu____3132 =
                let uu____3137 = FStar_TypeChecker_NBETerm.embed e_binders bs
                   in
                FStar_TypeChecker_NBETerm.as_arg uu____3137  in
              let uu____3138 =
                let uu____3145 =
                  let uu____3150 = FStar_TypeChecker_NBETerm.embed e_term t
                     in
                  FStar_TypeChecker_NBETerm.as_arg uu____3150  in
                let uu____3151 =
                  let uu____3158 =
                    let uu____3163 =
                      let uu____3164 =
                        FStar_TypeChecker_NBETerm.e_list e_string_list  in
                      FStar_TypeChecker_NBETerm.embed uu____3164 dcs  in
                    FStar_TypeChecker_NBETerm.as_arg uu____3163  in
                  [uu____3158]  in
                uu____3145 :: uu____3151  in
              uu____3132 :: uu____3138  in
            uu____3117 :: uu____3125  in
          uu____3102 :: uu____3110  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv []
          uu____3101
    | FStar_Reflection_Data.Unk  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv [] []
     in
  let unembed_sigelt_view t =
    match t with
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____3216,(nm,uu____3218)::(us,uu____3220)::(bs,uu____3222)::
         (t1,uu____3224)::(dcs,uu____3226)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
        ->
        let uu____3261 = FStar_TypeChecker_NBETerm.unembed e_string_list nm
           in
        FStar_Util.bind_opt uu____3261
          (fun nm1  ->
             let uu____3275 =
               FStar_TypeChecker_NBETerm.unembed e_univ_names us  in
             FStar_Util.bind_opt uu____3275
               (fun us1  ->
                  let uu____3289 =
                    FStar_TypeChecker_NBETerm.unembed e_binders bs  in
                  FStar_Util.bind_opt uu____3289
                    (fun bs1  ->
                       let uu____3295 =
                         FStar_TypeChecker_NBETerm.unembed e_term t1  in
                       FStar_Util.bind_opt uu____3295
                         (fun t2  ->
                            let uu____3301 =
                              let uu____3308 =
                                FStar_TypeChecker_NBETerm.e_list
                                  e_string_list
                                 in
                              FStar_TypeChecker_NBETerm.unembed uu____3308
                                dcs
                               in
                            FStar_Util.bind_opt uu____3301
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____3340,(r,uu____3342)::(fvar1,uu____3344)::(univs1,uu____3346)::
         (ty,uu____3348)::(t1,uu____3350)::[])
        when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
        ->
        let uu____3385 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool
            r
           in
        FStar_Util.bind_opt uu____3385
          (fun r1  ->
             let uu____3391 = FStar_TypeChecker_NBETerm.unembed e_fv fvar1
                in
             FStar_Util.bind_opt uu____3391
               (fun fvar2  ->
                  let uu____3397 =
                    FStar_TypeChecker_NBETerm.unembed e_univ_names univs1  in
                  FStar_Util.bind_opt uu____3397
                    (fun univs2  ->
                       let uu____3411 =
                         FStar_TypeChecker_NBETerm.unembed e_term ty  in
                       FStar_Util.bind_opt uu____3411
                         (fun ty1  ->
                            let uu____3417 =
                              FStar_TypeChecker_NBETerm.unembed e_term t1  in
                            FStar_Util.bind_opt uu____3417
                              (fun t2  ->
                                 FStar_All.pipe_left
                                   (fun _0_44  ->
                                      FStar_Pervasives_Native.Some _0_44)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, univs2, ty1, t2)))))))
    | FStar_TypeChecker_NBETerm.FV (fv,uu____3427,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
    | uu____3442 ->
        ((let uu____3444 =
            let uu____3449 =
              let uu____3450 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____3450
               in
            (FStar_Errors.Warning_NotEmbedded, uu____3449)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3444);
         FStar_Pervasives_Native.None)
     in
  let uu____3451 =
    FStar_TypeChecker_NBETerm.mkFV
      FStar_Reflection_Data.fstar_refl_sigelt_view_fv [] []
     in
  mk_emb embed_sigelt_view unembed_sigelt_view uu____3451 
let (e_exp : FStar_Reflection_Data.exp FStar_TypeChecker_NBETerm.embedding) =
  let rec embed_exp e =
    match e with
    | FStar_Reflection_Data.Unit  ->
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.fv [] []
    | FStar_Reflection_Data.Var i ->
        let uu____3469 =
          let uu____3470 =
            FStar_TypeChecker_NBETerm.as_arg
              (FStar_TypeChecker_NBETerm.Constant
                 (FStar_TypeChecker_NBETerm.Int i))
             in
          [uu____3470]  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv []
          uu____3469
    | FStar_Reflection_Data.Mult (e1,e2) ->
        let uu____3485 =
          let uu____3486 =
            let uu____3491 = embed_exp e1  in
            FStar_TypeChecker_NBETerm.as_arg uu____3491  in
          let uu____3492 =
            let uu____3499 =
              let uu____3504 = embed_exp e2  in
              FStar_TypeChecker_NBETerm.as_arg uu____3504  in
            [uu____3499]  in
          uu____3486 :: uu____3492  in
        FStar_TypeChecker_NBETerm.mkFV
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv []
          uu____3485
     in
  let rec unembed_exp t =
    match t with
    | FStar_TypeChecker_NBETerm.FV (fv,uu____3528,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
        -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
    | FStar_TypeChecker_NBETerm.FV (fv,uu____3544,(i,uu____3546)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
        ->
        let uu____3565 =
          FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int i
           in
        FStar_Util.bind_opt uu____3565
          (fun i1  ->
             FStar_All.pipe_left
               (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
               (FStar_Reflection_Data.Var i1))
    | FStar_TypeChecker_NBETerm.FV
        (fv,uu____3573,(e1,uu____3575)::(e2,uu____3577)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
        ->
        let uu____3600 = unembed_exp e1  in
        FStar_Util.bind_opt uu____3600
          (fun e11  ->
             let uu____3606 = unembed_exp e2  in
             FStar_Util.bind_opt uu____3606
               (fun e21  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Mult (e11, e21))))
    | uu____3613 ->
        ((let uu____3615 =
            let uu____3620 =
              let uu____3621 = FStar_TypeChecker_NBETerm.t_to_string t  in
              FStar_Util.format1 "Not an embedded exp: %s" uu____3621  in
            (FStar_Errors.Warning_NotEmbedded, uu____3620)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____3615);
         FStar_Pervasives_Native.None)
     in
  let uu____3622 =
    FStar_TypeChecker_NBETerm.mkFV FStar_Reflection_Data.fstar_refl_exp_fv []
      []
     in
  mk_emb embed_exp unembed_exp uu____3622 
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.e_tuple2 e_bv e_aqualv 
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding) = e_term 
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_TypeChecker_NBETerm.embedding)
  = FStar_TypeChecker_NBETerm.e_list e_attribute 