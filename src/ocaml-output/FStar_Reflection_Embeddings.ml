open Prims
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____25 =
      let uu____26 = FStar_Syntax_Subst.compress t  in
      uu____26.FStar_Syntax_Syntax.n  in
    match uu____25 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____32 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____32
    | uu____33 ->
        let uu____34 =
          if w
          then
            let uu____35 =
              let uu____40 =
                let uu____41 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____41  in
              (FStar_Errors.Warning_NotEmbedded, uu____40)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____35
          else ()  in
        FStar_Pervasives_Native.None
     in
  FStar_Syntax_Embeddings.mk_emb embed_bv unembed_bv
    FStar_Reflection_Data.fstar_refl_bv
  
let (e_binder : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding)
  =
  let embed_binder rng b =
    FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng)
     in
  let unembed_binder w t =
    let uu____67 =
      let uu____68 = FStar_Syntax_Subst.compress t  in
      uu____68.FStar_Syntax_Syntax.n  in
    match uu____67 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____74 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____74
    | uu____75 ->
        let uu____76 =
          if w
          then
            let uu____77 =
              let uu____82 =
                let uu____83 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____83  in
              (FStar_Errors.Warning_NotEmbedded, uu____82)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____77
          else ()  in
        FStar_Pervasives_Native.None
     in
  FStar_Syntax_Embeddings.mk_emb embed_binder unembed_binder
    FStar_Reflection_Data.fstar_refl_binder
  
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
          let uu____130 = f x  in
          FStar_Util.bind_opt uu____130
            (fun x1  ->
               let uu____138 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____138
                 (fun xs1  -> FStar_Pervasives_Native.Some (x1 :: xs1)))
  
let (e_term_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term rng t =
      let qi =
        {
          FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
          FStar_Syntax_Syntax.antiquotes = aq
        }  in
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (t, qi))
        FStar_Pervasives_Native.None rng
       in
    let rec unembed_term w t =
      let apply_antiquotes t1 aq1 =
        let uu____196 =
          mapM_opt
            (fun uu____213  ->
               match uu____213 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____236 = unembed_term w e  in
                      FStar_Util.bind_opt uu____236
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1))))) aq1
           in
        FStar_Util.bind_opt uu____196
          (fun s  ->
             let uu____248 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____248)
         in
      let uu____249 =
        let uu____250 = FStar_Syntax_Subst.compress t  in
        uu____250.FStar_Syntax_Syntax.n  in
      match uu____249 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____261 ->
          let uu____262 =
            if w
            then
              let uu____263 =
                let uu____268 =
                  let uu____269 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____269  in
                (FStar_Errors.Warning_NotEmbedded, uu____268)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____263
            else ()  in
          FStar_Pervasives_Native.None
       in
    FStar_Syntax_Embeddings.mk_emb embed_term unembed_term
      FStar_Syntax_Syntax.t_term
  
let (e_term : FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding) =
  e_term_aq [] 
let (e_aqualv :
  FStar_Reflection_Data.aqualv FStar_Syntax_Embeddings.embedding) =
  let embed_aqualv rng q =
    let r =
      match q with
      | FStar_Reflection_Data.Q_Explicit  ->
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Q_Implicit  ->
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.t
       in
    let uu___53_293 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___53_293.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___53_293.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____308 = FStar_Syntax_Util.head_and_args t1  in
    match uu____308 with
    | (hd1,args) ->
        let uu____347 =
          let uu____360 =
            let uu____361 = FStar_Syntax_Util.un_uinst hd1  in
            uu____361.FStar_Syntax_Syntax.n  in
          (uu____360, args)  in
        (match uu____347 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____404 ->
             let uu____417 =
               if w
               then
                 let uu____418 =
                   let uu____423 =
                     let uu____424 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____424
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____423)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____418
               else ()  in
             FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_aqualv unembed_aqualv
    FStar_Reflection_Data.fstar_refl_aqualv
  
let (e_binders :
  FStar_Syntax_Syntax.binder Prims.list FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_list e_binder 
let (e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings.embedding) =
  let embed_fv rng fv =
    FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
     in
  let unembed_fv w t =
    let uu____454 =
      let uu____455 = FStar_Syntax_Subst.compress t  in
      uu____455.FStar_Syntax_Syntax.n  in
    match uu____454 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____461 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____461
    | uu____462 ->
        let uu____463 =
          if w
          then
            let uu____464 =
              let uu____469 =
                let uu____470 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____470  in
              (FStar_Errors.Warning_NotEmbedded, uu____469)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____464
          else ()  in
        FStar_Pervasives_Native.None
     in
  FStar_Syntax_Embeddings.mk_emb embed_fv unembed_fv
    FStar_Reflection_Data.fstar_refl_fv
  
let (e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding) =
  let embed_comp rng c =
    FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng)
     in
  let unembed_comp w t =
    let uu____496 =
      let uu____497 = FStar_Syntax_Subst.compress t  in
      uu____497.FStar_Syntax_Syntax.n  in
    match uu____496 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____503 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____503
    | uu____504 ->
        let uu____505 =
          if w
          then
            let uu____506 =
              let uu____511 =
                let uu____512 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____512  in
              (FStar_Errors.Warning_NotEmbedded, uu____511)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____506
          else ()  in
        FStar_Pervasives_Native.None
     in
  FStar_Syntax_Embeddings.mk_emb embed_comp unembed_comp
    FStar_Reflection_Data.fstar_refl_comp
  
let (e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding) =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng)
     in
  let unembed_env w t =
    let uu____538 =
      let uu____539 = FStar_Syntax_Subst.compress t  in
      uu____539.FStar_Syntax_Syntax.n  in
    match uu____538 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____545 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____545
    | uu____546 ->
        let uu____547 =
          if w
          then
            let uu____548 =
              let uu____553 =
                let uu____554 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____554  in
              (FStar_Errors.Warning_NotEmbedded, uu____553)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____548
          else ()  in
        FStar_Pervasives_Native.None
     in
  FStar_Syntax_Embeddings.mk_emb embed_env unembed_env
    FStar_Reflection_Data.fstar_refl_env
  
let (e_const :
  FStar_Reflection_Data.vconst FStar_Syntax_Embeddings.embedding) =
  let embed_const rng c =
    let r =
      match c with
      | FStar_Reflection_Data.C_Unit  ->
          FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_True  ->
          FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_False  ->
          FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Int i ->
          let uu____569 =
            let uu____572 =
              let uu____573 =
                let uu____574 =
                  let uu____575 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____575  in
                FStar_Syntax_Syntax.as_arg uu____574  in
              [uu____573]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____572
             in
          uu____569 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____579 =
            let uu____582 =
              let uu____583 =
                let uu____584 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____584  in
              [uu____583]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____582
             in
          uu____579 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___54_587 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___54_587.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___54_587.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____602 = FStar_Syntax_Util.head_and_args t1  in
    match uu____602 with
    | (hd1,args) ->
        let uu____641 =
          let uu____654 =
            let uu____655 = FStar_Syntax_Util.un_uinst hd1  in
            uu____655.FStar_Syntax_Syntax.n  in
          (uu____654, args)  in
        (match uu____641 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____715)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____740 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____740
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____749)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____774 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____774
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                    (FStar_Reflection_Data.C_String s1))
         | uu____781 ->
             let uu____794 =
               if w
               then
                 let uu____795 =
                   let uu____800 =
                     let uu____801 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____801
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____800)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____795
               else ()  in
             FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____809  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____820 =
            let uu____823 =
              let uu____824 =
                let uu____825 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____825  in
              [uu____824]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____823
             in
          uu____820 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____834 =
            let uu____837 =
              let uu____838 =
                let uu____839 = FStar_Syntax_Embeddings.embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____839  in
              let uu____840 =
                let uu____843 =
                  let uu____844 =
                    let uu____845 =
                      let uu____850 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____850  in
                    FStar_Syntax_Embeddings.embed uu____845 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____844  in
                [uu____843]  in
              uu____838 :: uu____840  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____837
             in
          uu____834 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____858 =
            let uu____861 =
              let uu____862 =
                let uu____863 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____863  in
              [uu____862]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____861
             in
          uu____858 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____867 =
            let uu____870 =
              let uu____871 =
                let uu____872 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____872  in
              [uu____871]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____870
             in
          uu____867 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____877 =
            let uu____880 =
              let uu____881 =
                let uu____882 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____882  in
              let uu____883 =
                let uu____886 =
                  let uu____887 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____887  in
                [uu____886]  in
              uu____881 :: uu____883  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____880
             in
          uu____877 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____904 = FStar_Syntax_Util.head_and_args t1  in
      match uu____904 with
      | (hd1,args) ->
          let uu____943 =
            let uu____956 =
              let uu____957 = FStar_Syntax_Util.un_uinst hd1  in
              uu____957.FStar_Syntax_Syntax.n  in
            (uu____956, args)  in
          (match uu____943 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____972)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____997 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____997
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1006)::(ps,uu____1008)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1043 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____1043
                 (fun f1  ->
                    let uu____1049 =
                      let uu____1054 =
                        let uu____1059 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1059  in
                      FStar_Syntax_Embeddings.unembed uu____1054 ps  in
                    FStar_Util.bind_opt uu____1049
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1076)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1101 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1101
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1110)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1135 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1135
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1144)::(t2,uu____1146)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1181 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1181
                 (fun bv1  ->
                    let uu____1187 =
                      FStar_Syntax_Embeddings.unembed e_term t2  in
                    FStar_Util.bind_opt uu____1187
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1194 ->
               let uu____1207 =
                 if w
                 then
                   let uu____1208 =
                     let uu____1213 =
                       let uu____1214 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1214
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1213)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1208
                 else ()  in
               FStar_Pervasives_Native.None)
       in
    FStar_Syntax_Embeddings.mk_emb embed_pattern unembed_pattern
      FStar_Reflection_Data.fstar_refl_pattern
  
let (e_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  e_pattern' () 
let (e_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_tuple2 e_pattern e_term 
let (e_argv :
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_tuple2 e_term e_aqualv 
let (e_branch_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1241 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1241
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1255 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1255 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1275 =
            let uu____1278 =
              let uu____1279 =
                let uu____1280 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1280  in
              [uu____1279]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1278
             in
          uu____1275 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1284 =
            let uu____1287 =
              let uu____1288 =
                let uu____1289 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1289  in
              [uu____1288]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1287
             in
          uu____1284 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1293 =
            let uu____1296 =
              let uu____1297 =
                let uu____1298 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1298  in
              [uu____1297]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1296
             in
          uu____1293 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1303 =
            let uu____1306 =
              let uu____1307 =
                let uu____1308 =
                  let uu____1309 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1309 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1308  in
              let uu____1312 =
                let uu____1315 =
                  let uu____1316 =
                    let uu____1317 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1317 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1316  in
                [uu____1315]  in
              uu____1307 :: uu____1312  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1306
             in
          uu____1303 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1332 =
            let uu____1335 =
              let uu____1336 =
                let uu____1337 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1337  in
              let uu____1338 =
                let uu____1341 =
                  let uu____1342 =
                    let uu____1343 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1343 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1342  in
                [uu____1341]  in
              uu____1336 :: uu____1338  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1335
             in
          uu____1332 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1350 =
            let uu____1353 =
              let uu____1354 =
                let uu____1355 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1355  in
              let uu____1356 =
                let uu____1359 =
                  let uu____1360 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1360  in
                [uu____1359]  in
              uu____1354 :: uu____1356  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1353
             in
          uu____1350 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1364 =
            let uu____1367 =
              let uu____1368 =
                let uu____1369 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1369  in
              [uu____1368]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____1367
             in
          uu____1364 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1374 =
            let uu____1377 =
              let uu____1378 =
                let uu____1379 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1379  in
              let uu____1380 =
                let uu____1383 =
                  let uu____1384 =
                    let uu____1385 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1385 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1384  in
                [uu____1383]  in
              uu____1378 :: uu____1380  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____1377
             in
          uu____1374 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1391 =
            let uu____1394 =
              let uu____1395 =
                let uu____1396 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____1396  in
              [uu____1395]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____1394
             in
          uu____1391 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1401 =
            let uu____1404 =
              let uu____1405 =
                let uu____1406 =
                  FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int
                    rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____1406  in
              let uu____1407 =
                let uu____1410 =
                  let uu____1411 =
                    let uu____1412 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1412 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1411  in
                [uu____1410]  in
              uu____1405 :: uu____1407  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____1404
             in
          uu____1401 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1421 =
            let uu____1424 =
              let uu____1425 =
                let uu____1426 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1426  in
              let uu____1427 =
                let uu____1430 =
                  let uu____1431 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____1431  in
                let uu____1432 =
                  let uu____1435 =
                    let uu____1436 =
                      let uu____1437 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____1437 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____1436  in
                  let uu____1440 =
                    let uu____1443 =
                      let uu____1444 =
                        let uu____1445 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____1445 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____1444  in
                    [uu____1443]  in
                  uu____1435 :: uu____1440  in
                uu____1430 :: uu____1432  in
              uu____1425 :: uu____1427  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____1424
             in
          uu____1421 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1456 =
            let uu____1459 =
              let uu____1460 =
                let uu____1461 =
                  let uu____1462 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1462 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____1461  in
              let uu____1465 =
                let uu____1468 =
                  let uu____1469 =
                    let uu____1470 =
                      let uu____1479 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____1479  in
                    FStar_Syntax_Embeddings.embed uu____1470 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____1469  in
                [uu____1468]  in
              uu____1460 :: uu____1465  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____1459
             in
          uu____1456 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____1505 =
            let uu____1508 =
              let uu____1509 =
                let uu____1510 =
                  let uu____1511 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1511 rng e  in
                FStar_Syntax_Syntax.as_arg uu____1510  in
              let uu____1514 =
                let uu____1517 =
                  let uu____1518 =
                    let uu____1519 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1519 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1518  in
                let uu____1522 =
                  let uu____1525 =
                    let uu____1526 =
                      let uu____1527 =
                        let uu____1532 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____1532  in
                      FStar_Syntax_Embeddings.embed uu____1527 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____1526  in
                  [uu____1525]  in
                uu____1517 :: uu____1522  in
              uu____1509 :: uu____1514  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____1508
             in
          uu____1505 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____1546 =
            let uu____1549 =
              let uu____1550 =
                let uu____1551 =
                  let uu____1552 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1552 rng e  in
                FStar_Syntax_Syntax.as_arg uu____1551  in
              let uu____1555 =
                let uu____1558 =
                  let uu____1559 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1559  in
                let uu____1560 =
                  let uu____1563 =
                    let uu____1564 =
                      let uu____1565 =
                        let uu____1570 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____1570  in
                      FStar_Syntax_Embeddings.embed uu____1565 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____1564  in
                  [uu____1563]  in
                uu____1558 :: uu____1560  in
              uu____1550 :: uu____1555  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____1549
             in
          uu____1546 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___55_1577 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___55_1577.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___55_1577.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____1591 = FStar_Syntax_Util.head_and_args t  in
      match uu____1591 with
      | (hd1,args) ->
          let uu____1630 =
            let uu____1643 =
              let uu____1644 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1644.FStar_Syntax_Syntax.n  in
            (uu____1643, args)  in
          (match uu____1630 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1659)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____1684 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____1684
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1693)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____1718 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____1718
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1727)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____1752 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____1752
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____1761)::(r,uu____1763)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____1798 = FStar_Syntax_Embeddings.unembed e_term l  in
               FStar_Util.bind_opt uu____1798
                 (fun l1  ->
                    let uu____1804 = FStar_Syntax_Embeddings.unembed e_argv r
                       in
                    FStar_Util.bind_opt uu____1804
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1833)::(t1,uu____1835)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____1870 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____1870
                 (fun b1  ->
                    let uu____1876 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____1876
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1885)::(t1,uu____1887)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____1922 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____1922
                 (fun b1  ->
                    let uu____1928 =
                      FStar_Syntax_Embeddings.unembed e_comp t1  in
                    FStar_Util.bind_opt uu____1928
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1937)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____1962 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____1962
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1971)::(t1,uu____1973)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____2008 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____2008
                 (fun b1  ->
                    let uu____2014 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2014
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2023)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____2048 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____2048
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____2057)::(t1,uu____2059)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____2094 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____2094
                 (fun u1  ->
                    let uu____2100 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2100
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                           (FStar_Reflection_Data.Tv_Uvar (u1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____2109)::(b,uu____2111)::(t1,uu____2113)::(t2,uu____2115)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____2170 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____2170
                 (fun r1  ->
                    let uu____2176 = FStar_Syntax_Embeddings.unembed e_bv b
                       in
                    FStar_Util.bind_opt uu____2176
                      (fun b1  ->
                         let uu____2182 =
                           FStar_Syntax_Embeddings.unembed e_term t1  in
                         FStar_Util.bind_opt uu____2182
                           (fun t11  ->
                              let uu____2188 =
                                FStar_Syntax_Embeddings.unembed e_term t2  in
                              FStar_Util.bind_opt uu____2188
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_34  ->
                                        FStar_Pervasives_Native.Some _0_34)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____2197)::(brs,uu____2199)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____2234 = FStar_Syntax_Embeddings.unembed e_term t1  in
               FStar_Util.bind_opt uu____2234
                 (fun t2  ->
                    let uu____2240 =
                      let uu____2249 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed uu____2249 brs  in
                    FStar_Util.bind_opt uu____2240
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2292)::(t1,uu____2294)::(tacopt,uu____2296)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____2341 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2341
                 (fun e1  ->
                    let uu____2347 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2347
                      (fun t2  ->
                         let uu____2353 =
                           let uu____2358 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2358 tacopt
                            in
                         FStar_Util.bind_opt uu____2353
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_36  ->
                                   FStar_Pervasives_Native.Some _0_36)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2377)::(c,uu____2379)::(tacopt,uu____2381)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____2426 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2426
                 (fun e1  ->
                    let uu____2432 = FStar_Syntax_Embeddings.unembed e_comp c
                       in
                    FStar_Util.bind_opt uu____2432
                      (fun c1  ->
                         let uu____2438 =
                           let uu____2443 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2443 tacopt
                            in
                         FStar_Util.bind_opt uu____2438
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_37  ->
                                   FStar_Pervasives_Native.Some _0_37)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____2477 ->
               let uu____2490 =
                 if w
                 then
                   let uu____2491 =
                     let uu____2496 =
                       let uu____2497 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____2497
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2496)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____2491
                 else ()  in
               FStar_Pervasives_Native.None)
       in
    FStar_Syntax_Embeddings.mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____2520 =
      let uu____2523 =
        let uu____2524 =
          let uu____2525 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____2525  in
        let uu____2526 =
          let uu____2529 =
            let uu____2530 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____2530  in
          let uu____2531 =
            let uu____2534 =
              let uu____2535 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____2535  in
            [uu____2534]  in
          uu____2529 :: uu____2531  in
        uu____2524 :: uu____2526  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____2523
       in
    uu____2520 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2552 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2552 with
    | (hd1,args) ->
        let uu____2591 =
          let uu____2604 =
            let uu____2605 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2605.FStar_Syntax_Syntax.n  in
          (uu____2604, args)  in
        (match uu____2591 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2620)::(idx,uu____2622)::(s,uu____2624)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2669 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____2669
               (fun nm1  ->
                  let uu____2675 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____2675
                    (fun idx1  ->
                       let uu____2681 =
                         FStar_Syntax_Embeddings.unembed e_term s  in
                       FStar_Util.bind_opt uu____2681
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_39  ->
                                 FStar_Pervasives_Native.Some _0_39)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2688 ->
             let uu____2701 =
               if w
               then
                 let uu____2702 =
                   let uu____2707 =
                     let uu____2708 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____2708
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2707)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2702
               else ()  in
             FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding) =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____2727 =
          let uu____2730 =
            let uu____2731 =
              let uu____2732 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____2732  in
            let uu____2733 =
              let uu____2736 =
                let uu____2737 =
                  let uu____2738 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____2738 rng md  in
                FStar_Syntax_Syntax.as_arg uu____2737  in
              [uu____2736]  in
            uu____2731 :: uu____2733  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____2730
           in
        uu____2727 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____2752 =
          let uu____2755 =
            let uu____2756 =
              let uu____2757 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____2757  in
            let uu____2758 =
              let uu____2761 =
                let uu____2762 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____2762  in
              [uu____2761]  in
            uu____2756 :: uu____2758  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____2755
           in
        uu____2752 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___56_2765 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___56_2765.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___56_2765.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2780 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2780 with
    | (hd1,args) ->
        let uu____2819 =
          let uu____2832 =
            let uu____2833 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2833.FStar_Syntax_Syntax.n  in
          (uu____2832, args)  in
        (match uu____2819 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2848)::(md,uu____2850)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2885 = FStar_Syntax_Embeddings.unembed e_term t2  in
             FStar_Util.bind_opt uu____2885
               (fun t3  ->
                  let uu____2891 =
                    let uu____2896 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed uu____2896 md  in
                  FStar_Util.bind_opt uu____2891
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2915)::(post,uu____2917)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2952 = FStar_Syntax_Embeddings.unembed e_term pre  in
             FStar_Util.bind_opt uu____2952
               (fun pre1  ->
                  let uu____2958 =
                    FStar_Syntax_Embeddings.unembed e_term post  in
                  FStar_Util.bind_opt uu____2958
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
               FStar_Reflection_Data.C_Unknown
         | uu____2982 ->
             let uu____2995 =
               if w
               then
                 let uu____2996 =
                   let uu____3001 =
                     let uu____3002 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____3002
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3001)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2996
               else ()  in
             FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_comp_view unembed_comp_view
    FStar_Reflection_Data.fstar_refl_comp_view
  
let (e_order : FStar_Order.order FStar_Syntax_Embeddings.embedding) =
  let embed_order rng o =
    let r =
      match o with
      | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
      | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
      | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt  in
    let uu___57_3016 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___57_3016.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___57_3016.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3031 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3031 with
    | (hd1,args) ->
        let uu____3070 =
          let uu____3083 =
            let uu____3084 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3084.FStar_Syntax_Syntax.n  in
          (uu____3083, args)  in
        (match uu____3070 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Gt
         | uu____3142 ->
             let uu____3155 =
               if w
               then
                 let uu____3156 =
                   let uu____3161 =
                     let uu____3162 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____3162
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3161)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3156
               else ()  in
             FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_order unembed_order
    FStar_Syntax_Syntax.t_order
  
let (e_sigelt : FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings.embedding)
  =
  let embed_sigelt rng se =
    FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng)
     in
  let unembed_sigelt w t =
    let uu____3188 =
      let uu____3189 = FStar_Syntax_Subst.compress t  in
      uu____3189.FStar_Syntax_Syntax.n  in
    match uu____3188 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____3195 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____3195
    | uu____3196 ->
        let uu____3197 =
          if w
          then
            let uu____3198 =
              let uu____3203 =
                let uu____3204 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____3204
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3203)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3198
          else ()  in
        FStar_Pervasives_Native.None
     in
  FStar_Syntax_Embeddings.mk_emb embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt
  
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,ty,t) ->
        let uu____3221 =
          let uu____3224 =
            let uu____3225 =
              let uu____3226 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____3226  in
            let uu____3227 =
              let uu____3230 =
                let uu____3231 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____3231  in
              let uu____3232 =
                let uu____3235 =
                  let uu____3236 =
                    FStar_Syntax_Embeddings.embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3236  in
                let uu____3237 =
                  let uu____3240 =
                    let uu____3241 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3241  in
                  [uu____3240]  in
                uu____3235 :: uu____3237  in
              uu____3230 :: uu____3232  in
            uu____3225 :: uu____3227  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____3224
           in
        uu____3221 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3246 =
          let uu____3249 =
            let uu____3250 =
              let uu____3251 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3251  in
            let uu____3254 =
              let uu____3257 =
                let uu____3258 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____3258  in
              [uu____3257]  in
            uu____3250 :: uu____3254  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____3249
           in
        uu____3246 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3273 =
          let uu____3276 =
            let uu____3277 =
              let uu____3278 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3278  in
            let uu____3281 =
              let uu____3284 =
                let uu____3285 =
                  FStar_Syntax_Embeddings.embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____3285  in
              let uu____3288 =
                let uu____3291 =
                  let uu____3292 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____3292  in
                let uu____3293 =
                  let uu____3296 =
                    let uu____3297 =
                      let uu____3298 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      FStar_Syntax_Embeddings.embed uu____3298 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____3297  in
                  [uu____3296]  in
                uu____3291 :: uu____3293  in
              uu____3284 :: uu____3288  in
            uu____3277 :: uu____3281  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____3276
           in
        uu____3273 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___58_3313 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___58_3313.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___58_3313.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3328 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3328 with
    | (hd1,args) ->
        let uu____3367 =
          let uu____3380 =
            let uu____3381 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3381.FStar_Syntax_Syntax.n  in
          (uu____3380, args)  in
        (match uu____3367 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3396)::(bs,uu____3398)::(t2,uu____3400)::(dcs,uu____3402)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3457 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____3457
               (fun nm1  ->
                  let uu____3471 =
                    FStar_Syntax_Embeddings.unembed e_binders bs  in
                  FStar_Util.bind_opt uu____3471
                    (fun bs1  ->
                       let uu____3485 =
                         FStar_Syntax_Embeddings.unembed e_term t2  in
                       FStar_Util.bind_opt uu____3485
                         (fun t3  ->
                            let uu____3491 =
                              let uu____3498 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_string_list
                                 in
                              FStar_Syntax_Embeddings.unembed uu____3498 dcs
                               in
                            FStar_Util.bind_opt uu____3491
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____3533)::(fvar1,uu____3535)::(ty,uu____3537)::(t2,uu____3539)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3594 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_bool
                 r
                in
             FStar_Util.bind_opt uu____3594
               (fun r1  ->
                  let uu____3600 = FStar_Syntax_Embeddings.unembed e_fv fvar1
                     in
                  FStar_Util.bind_opt uu____3600
                    (fun fvar2  ->
                       let uu____3606 =
                         FStar_Syntax_Embeddings.unembed e_term ty  in
                       FStar_Util.bind_opt uu____3606
                         (fun ty1  ->
                            let uu____3612 =
                              FStar_Syntax_Embeddings.unembed e_term t2  in
                            FStar_Util.bind_opt uu____3612
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_44  ->
                                      FStar_Pervasives_Native.Some _0_44)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3634 ->
             let uu____3647 =
               if w
               then
                 let uu____3648 =
                   let uu____3653 =
                     let uu____3654 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____3654
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3653)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3648
               else ()  in
             FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_Data.fstar_refl_sigelt_view
  
let (e_exp : FStar_Reflection_Data.exp FStar_Syntax_Embeddings.embedding) =
  let rec embed_exp rng e =
    let r =
      match e with
      | FStar_Reflection_Data.Unit  ->
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Var i ->
          let uu____3669 =
            let uu____3672 =
              let uu____3673 =
                let uu____3674 =
                  let uu____3675 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____3675  in
                FStar_Syntax_Syntax.as_arg uu____3674  in
              [uu____3673]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____3672
             in
          uu____3669 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____3680 =
            let uu____3683 =
              let uu____3684 =
                let uu____3685 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____3685  in
              let uu____3686 =
                let uu____3689 =
                  let uu____3690 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____3690  in
                [uu____3689]  in
              uu____3684 :: uu____3686  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____3683
             in
          uu____3680 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___59_3693 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___59_3693.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___59_3693.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3708 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3708 with
    | (hd1,args) ->
        let uu____3747 =
          let uu____3760 =
            let uu____3761 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3761.FStar_Syntax_Syntax.n  in
          (uu____3760, args)  in
        (match uu____3747 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____3791)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____3816 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____3816
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____3825)::(e2,uu____3827)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____3862 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____3862
               (fun e11  ->
                  let uu____3868 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____3868
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____3875 ->
             let uu____3888 =
               if w
               then
                 let uu____3889 =
                   let uu____3894 =
                     let uu____3895 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____3895
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3894)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3889
               else ()  in
             FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_exp unembed_exp
    FStar_Reflection_Data.fstar_refl_exp
  
let (e_binder_view :
  (FStar_Syntax_Syntax.bv,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3909 =
      let uu____3912 =
        let uu____3913 =
          let uu____3914 =
            let uu____3915 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____3915
             in
          FStar_Syntax_Syntax.as_arg uu____3914  in
        [uu____3913]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____3912
       in
    uu____3909 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3924 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____3924 with
    | (bv,aq) ->
        let uu____3931 =
          let uu____3934 =
            let uu____3935 =
              let uu____3936 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____3936  in
            let uu____3937 =
              let uu____3940 =
                let uu____3941 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____3941  in
              [uu____3940]  in
            uu____3935 :: uu____3937  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____3934
           in
        uu____3931 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3950 =
      let uu____3953 =
        let uu____3954 =
          let uu____3955 =
            let uu____3956 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____3961 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____3956
              i.FStar_Syntax_Syntax.rng uu____3961
             in
          FStar_Syntax_Syntax.as_arg uu____3955  in
        [uu____3954]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____3953
       in
    uu____3950 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3974 =
      let uu____3977 =
        let uu____3978 =
          let uu____3979 =
            let uu____3980 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____3980
             in
          FStar_Syntax_Syntax.as_arg uu____3979  in
        [uu____3978]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____3977
       in
    uu____3974 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3994 =
      let uu____3997 =
        let uu____3998 =
          let uu____3999 =
            let uu____4000 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____4000
             in
          FStar_Syntax_Syntax.as_arg uu____3999  in
        [uu____3998]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____3997
       in
    uu____3994 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  