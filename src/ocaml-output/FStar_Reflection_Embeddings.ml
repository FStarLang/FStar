open Prims
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____21 =
      let uu____22 = FStar_Syntax_Subst.compress t  in
      uu____22.FStar_Syntax_Syntax.n  in
    match uu____21 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____28 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____28
    | uu____29 ->
        (if w
         then
           (let uu____31 =
              let uu____36 =
                let uu____37 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____37  in
              (FStar_Errors.Warning_NotEmbedded, uu____36)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____31)
         else ();
         FStar_Pervasives_Native.None)
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
    let uu____59 =
      let uu____60 = FStar_Syntax_Subst.compress t  in
      uu____60.FStar_Syntax_Syntax.n  in
    match uu____59 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____66 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____66
    | uu____67 ->
        (if w
         then
           (let uu____69 =
              let uu____74 =
                let uu____75 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____75  in
              (FStar_Errors.Warning_NotEmbedded, uu____74)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____69)
         else ();
         FStar_Pervasives_Native.None)
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
          let uu____116 = f x  in
          FStar_Util.bind_opt uu____116
            (fun x1  ->
               let uu____124 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____124
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
        let uu____174 =
          mapM_opt
            (fun uu____191  ->
               match uu____191 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____214 = unembed_term w e  in
                      FStar_Util.bind_opt uu____214
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1))))) aq1
           in
        FStar_Util.bind_opt uu____174
          (fun s  ->
             let uu____226 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____226)
         in
      let uu____227 =
        let uu____228 = FStar_Syntax_Subst.compress t  in
        uu____228.FStar_Syntax_Syntax.n  in
      match uu____227 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____239 ->
          (if w
           then
             (let uu____241 =
                let uu____246 =
                  let uu____247 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____247  in
                (FStar_Errors.Warning_NotEmbedded, uu____246)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____241)
           else ();
           FStar_Pervasives_Native.None)
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
    let uu___53_269 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___53_269.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___53_269.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____282 = FStar_Syntax_Util.head_and_args t1  in
    match uu____282 with
    | (hd1,args) ->
        let uu____321 =
          let uu____334 =
            let uu____335 = FStar_Syntax_Util.un_uinst hd1  in
            uu____335.FStar_Syntax_Syntax.n  in
          (uu____334, args)  in
        (match uu____321 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____378 ->
             (if w
              then
                (let uu____392 =
                   let uu____397 =
                     let uu____398 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____398
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____397)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____392)
              else ();
              FStar_Pervasives_Native.None))
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
    let uu____424 =
      let uu____425 = FStar_Syntax_Subst.compress t  in
      uu____425.FStar_Syntax_Syntax.n  in
    match uu____424 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____431 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____431
    | uu____432 ->
        (if w
         then
           (let uu____434 =
              let uu____439 =
                let uu____440 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____440  in
              (FStar_Errors.Warning_NotEmbedded, uu____439)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____434)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_fv unembed_fv
    FStar_Reflection_Data.fstar_refl_fv
  
let (e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding) =
  let embed_comp rng c =
    FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng)
     in
  let unembed_comp w t =
    let uu____462 =
      let uu____463 = FStar_Syntax_Subst.compress t  in
      uu____463.FStar_Syntax_Syntax.n  in
    match uu____462 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____469 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____469
    | uu____470 ->
        (if w
         then
           (let uu____472 =
              let uu____477 =
                let uu____478 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____478  in
              (FStar_Errors.Warning_NotEmbedded, uu____477)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____472)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_comp unembed_comp
    FStar_Reflection_Data.fstar_refl_comp
  
let (e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding) =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng)
     in
  let unembed_env w t =
    let uu____500 =
      let uu____501 = FStar_Syntax_Subst.compress t  in
      uu____501.FStar_Syntax_Syntax.n  in
    match uu____500 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____507 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____507
    | uu____508 ->
        (if w
         then
           (let uu____510 =
              let uu____515 =
                let uu____516 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____516  in
              (FStar_Errors.Warning_NotEmbedded, uu____515)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____510)
         else ();
         FStar_Pervasives_Native.None)
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
          let uu____529 =
            let uu____530 =
              let uu____531 =
                let uu____532 =
                  let uu____533 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____533  in
                FStar_Syntax_Syntax.as_arg uu____532  in
              [uu____531]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____530
             in
          uu____529 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____537 =
            let uu____538 =
              let uu____539 =
                let uu____540 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____540  in
              [uu____539]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____538
             in
          uu____537 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___54_543 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___54_543.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___54_543.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____556 = FStar_Syntax_Util.head_and_args t1  in
    match uu____556 with
    | (hd1,args) ->
        let uu____595 =
          let uu____608 =
            let uu____609 = FStar_Syntax_Util.un_uinst hd1  in
            uu____609.FStar_Syntax_Syntax.n  in
          (uu____608, args)  in
        (match uu____595 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____669)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____694 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____694
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____703)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____728 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____728
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____735 ->
             (if w
              then
                (let uu____749 =
                   let uu____754 =
                     let uu____755 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____755
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____754)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____749)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst
  
let rec (e_pattern' :
  Prims.unit ->
    FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding)
  =
  fun uu____761  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____770 =
            let uu____771 =
              let uu____772 =
                let uu____773 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____773  in
              [uu____772]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____771
             in
          uu____770 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____782 =
            let uu____783 =
              let uu____784 =
                let uu____785 = FStar_Syntax_Embeddings.embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____785  in
              let uu____786 =
                let uu____789 =
                  let uu____790 =
                    let uu____791 =
                      let uu____796 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____796  in
                    FStar_Syntax_Embeddings.embed uu____791 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____790  in
                [uu____789]  in
              uu____784 :: uu____786  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____783
             in
          uu____782 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____804 =
            let uu____805 =
              let uu____806 =
                let uu____807 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____807  in
              [uu____806]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____805
             in
          uu____804 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____811 =
            let uu____812 =
              let uu____813 =
                let uu____814 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____814  in
              [uu____813]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____812
             in
          uu____811 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____819 =
            let uu____820 =
              let uu____821 =
                let uu____822 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____822  in
              let uu____823 =
                let uu____826 =
                  let uu____827 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____827  in
                [uu____826]  in
              uu____821 :: uu____823  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____820
             in
          uu____819 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____842 = FStar_Syntax_Util.head_and_args t1  in
      match uu____842 with
      | (hd1,args) ->
          let uu____881 =
            let uu____894 =
              let uu____895 = FStar_Syntax_Util.un_uinst hd1  in
              uu____895.FStar_Syntax_Syntax.n  in
            (uu____894, args)  in
          (match uu____881 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____910)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____935 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____935
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____944)::(ps,uu____946)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____981 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____981
                 (fun f1  ->
                    let uu____987 =
                      let uu____992 =
                        let uu____997 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____997  in
                      FStar_Syntax_Embeddings.unembed uu____992 ps  in
                    FStar_Util.bind_opt uu____987
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1014)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1039 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1039
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1048)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1073 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1073
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1082)::(t2,uu____1084)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1119 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1119
                 (fun bv1  ->
                    let uu____1125 =
                      FStar_Syntax_Embeddings.unembed e_term t2  in
                    FStar_Util.bind_opt uu____1125
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1132 ->
               (if w
                then
                  (let uu____1146 =
                     let uu____1151 =
                       let uu____1152 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1152
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1151)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1146)
                else ();
                FStar_Pervasives_Native.None))
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
    let uu____1177 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1177
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1189 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1189 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1205 =
            let uu____1206 =
              let uu____1207 =
                let uu____1208 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1208  in
              [uu____1207]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1206
             in
          uu____1205 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1212 =
            let uu____1213 =
              let uu____1214 =
                let uu____1215 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1215  in
              [uu____1214]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1213
             in
          uu____1212 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1219 =
            let uu____1220 =
              let uu____1221 =
                let uu____1222 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1222  in
              [uu____1221]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1220
             in
          uu____1219 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1227 =
            let uu____1228 =
              let uu____1229 =
                let uu____1230 =
                  let uu____1231 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1231 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1230  in
              let uu____1234 =
                let uu____1237 =
                  let uu____1238 =
                    let uu____1239 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1239 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1238  in
                [uu____1237]  in
              uu____1229 :: uu____1234  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1228
             in
          uu____1227 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1254 =
            let uu____1255 =
              let uu____1256 =
                let uu____1257 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1257  in
              let uu____1258 =
                let uu____1261 =
                  let uu____1262 =
                    let uu____1263 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1263 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1262  in
                [uu____1261]  in
              uu____1256 :: uu____1258  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1255
             in
          uu____1254 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1270 =
            let uu____1271 =
              let uu____1272 =
                let uu____1273 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1273  in
              let uu____1274 =
                let uu____1277 =
                  let uu____1278 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1278  in
                [uu____1277]  in
              uu____1272 :: uu____1274  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1271
             in
          uu____1270 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1282 =
            let uu____1283 =
              let uu____1284 =
                let uu____1285 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1285  in
              [uu____1284]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____1283
             in
          uu____1282 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1290 =
            let uu____1291 =
              let uu____1292 =
                let uu____1293 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1293  in
              let uu____1294 =
                let uu____1297 =
                  let uu____1298 =
                    let uu____1299 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1299 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1298  in
                [uu____1297]  in
              uu____1292 :: uu____1294  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____1291
             in
          uu____1290 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1305 =
            let uu____1306 =
              let uu____1307 =
                let uu____1308 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____1308  in
              [uu____1307]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____1306
             in
          uu____1305 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1313 =
            let uu____1314 =
              let uu____1315 =
                let uu____1316 =
                  FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int
                    rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____1316  in
              let uu____1317 =
                let uu____1320 =
                  let uu____1321 =
                    let uu____1322 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1322 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1321  in
                [uu____1320]  in
              uu____1315 :: uu____1317  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____1314
             in
          uu____1313 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1331 =
            let uu____1332 =
              let uu____1333 =
                let uu____1334 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1334  in
              let uu____1335 =
                let uu____1338 =
                  let uu____1339 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____1339  in
                let uu____1340 =
                  let uu____1343 =
                    let uu____1344 =
                      let uu____1345 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____1345 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____1344  in
                  let uu____1348 =
                    let uu____1351 =
                      let uu____1352 =
                        let uu____1353 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____1353 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____1352  in
                    [uu____1351]  in
                  uu____1343 :: uu____1348  in
                uu____1338 :: uu____1340  in
              uu____1333 :: uu____1335  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____1332
             in
          uu____1331 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1364 =
            let uu____1365 =
              let uu____1366 =
                let uu____1367 =
                  let uu____1368 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1368 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____1367  in
              let uu____1371 =
                let uu____1374 =
                  let uu____1375 =
                    let uu____1376 =
                      let uu____1385 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____1385  in
                    FStar_Syntax_Embeddings.embed uu____1376 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____1375  in
                [uu____1374]  in
              uu____1366 :: uu____1371  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____1365
             in
          uu____1364 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____1411 =
            let uu____1412 =
              let uu____1413 =
                let uu____1414 =
                  let uu____1415 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1415 rng e  in
                FStar_Syntax_Syntax.as_arg uu____1414  in
              let uu____1418 =
                let uu____1421 =
                  let uu____1422 =
                    let uu____1423 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1423 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1422  in
                let uu____1426 =
                  let uu____1429 =
                    let uu____1430 =
                      let uu____1431 =
                        let uu____1436 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____1436  in
                      FStar_Syntax_Embeddings.embed uu____1431 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____1430  in
                  [uu____1429]  in
                uu____1421 :: uu____1426  in
              uu____1413 :: uu____1418  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____1412
             in
          uu____1411 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____1450 =
            let uu____1451 =
              let uu____1452 =
                let uu____1453 =
                  let uu____1454 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1454 rng e  in
                FStar_Syntax_Syntax.as_arg uu____1453  in
              let uu____1457 =
                let uu____1460 =
                  let uu____1461 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1461  in
                let uu____1462 =
                  let uu____1465 =
                    let uu____1466 =
                      let uu____1467 =
                        let uu____1472 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____1472  in
                      FStar_Syntax_Embeddings.embed uu____1467 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____1466  in
                  [uu____1465]  in
                uu____1460 :: uu____1462  in
              uu____1452 :: uu____1457  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____1451
             in
          uu____1450 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___55_1479 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___55_1479.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___55_1479.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____1491 = FStar_Syntax_Util.head_and_args t  in
      match uu____1491 with
      | (hd1,args) ->
          let uu____1530 =
            let uu____1543 =
              let uu____1544 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1544.FStar_Syntax_Syntax.n  in
            (uu____1543, args)  in
          (match uu____1530 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1559)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____1584 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____1584
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1593)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____1618 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____1618
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1627)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____1652 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____1652
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____1661)::(r,uu____1663)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____1698 = FStar_Syntax_Embeddings.unembed e_term l  in
               FStar_Util.bind_opt uu____1698
                 (fun l1  ->
                    let uu____1704 = FStar_Syntax_Embeddings.unembed e_argv r
                       in
                    FStar_Util.bind_opt uu____1704
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1733)::(t1,uu____1735)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____1770 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____1770
                 (fun b1  ->
                    let uu____1776 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____1776
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1785)::(t1,uu____1787)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____1822 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____1822
                 (fun b1  ->
                    let uu____1828 =
                      FStar_Syntax_Embeddings.unembed e_comp t1  in
                    FStar_Util.bind_opt uu____1828
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1837)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____1862 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____1862
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1871)::(t1,uu____1873)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____1908 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____1908
                 (fun b1  ->
                    let uu____1914 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____1914
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1923)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____1948 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____1948
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____1957)::(t1,uu____1959)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____1994 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____1994
                 (fun u1  ->
                    let uu____2000 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2000
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_56  -> FStar_Pervasives_Native.Some _0_56)
                           (FStar_Reflection_Data.Tv_Uvar (u1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____2009)::(b,uu____2011)::(t1,uu____2013)::(t2,uu____2015)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____2070 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____2070
                 (fun r1  ->
                    let uu____2076 = FStar_Syntax_Embeddings.unembed e_bv b
                       in
                    FStar_Util.bind_opt uu____2076
                      (fun b1  ->
                         let uu____2082 =
                           FStar_Syntax_Embeddings.unembed e_term t1  in
                         FStar_Util.bind_opt uu____2082
                           (fun t11  ->
                              let uu____2088 =
                                FStar_Syntax_Embeddings.unembed e_term t2  in
                              FStar_Util.bind_opt uu____2088
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_57  ->
                                        FStar_Pervasives_Native.Some _0_57)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____2097)::(brs,uu____2099)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____2134 = FStar_Syntax_Embeddings.unembed e_term t1  in
               FStar_Util.bind_opt uu____2134
                 (fun t2  ->
                    let uu____2140 =
                      let uu____2149 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed uu____2149 brs  in
                    FStar_Util.bind_opt uu____2140
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2192)::(t1,uu____2194)::(tacopt,uu____2196)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____2241 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2241
                 (fun e1  ->
                    let uu____2247 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2247
                      (fun t2  ->
                         let uu____2253 =
                           let uu____2258 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2258 tacopt
                            in
                         FStar_Util.bind_opt uu____2253
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_59  ->
                                   FStar_Pervasives_Native.Some _0_59)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2277)::(c,uu____2279)::(tacopt,uu____2281)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____2326 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2326
                 (fun e1  ->
                    let uu____2332 = FStar_Syntax_Embeddings.unembed e_comp c
                       in
                    FStar_Util.bind_opt uu____2332
                      (fun c1  ->
                         let uu____2338 =
                           let uu____2343 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2343 tacopt
                            in
                         FStar_Util.bind_opt uu____2338
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_60  ->
                                   FStar_Pervasives_Native.Some _0_60)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____2377 ->
               (if w
                then
                  (let uu____2391 =
                     let uu____2396 =
                       let uu____2397 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____2397
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2396)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____2391)
                else ();
                FStar_Pervasives_Native.None))
       in
    FStar_Syntax_Embeddings.mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____2418 =
      let uu____2419 =
        let uu____2420 =
          let uu____2421 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____2421  in
        let uu____2422 =
          let uu____2425 =
            let uu____2426 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____2426  in
          let uu____2427 =
            let uu____2430 =
              let uu____2431 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____2431  in
            [uu____2430]  in
          uu____2425 :: uu____2427  in
        uu____2420 :: uu____2422  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____2419
       in
    uu____2418 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2446 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2446 with
    | (hd1,args) ->
        let uu____2485 =
          let uu____2498 =
            let uu____2499 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2499.FStar_Syntax_Syntax.n  in
          (uu____2498, args)  in
        (match uu____2485 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2514)::(idx,uu____2516)::(s,uu____2518)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2563 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____2563
               (fun nm1  ->
                  let uu____2569 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____2569
                    (fun idx1  ->
                       let uu____2575 =
                         FStar_Syntax_Embeddings.unembed e_term s  in
                       FStar_Util.bind_opt uu____2575
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_62  ->
                                 FStar_Pervasives_Native.Some _0_62)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2582 ->
             (if w
              then
                (let uu____2596 =
                   let uu____2601 =
                     let uu____2602 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____2602
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2601)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2596)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding) =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____2619 =
          let uu____2620 =
            let uu____2621 =
              let uu____2622 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____2622  in
            let uu____2623 =
              let uu____2626 =
                let uu____2627 =
                  let uu____2628 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____2628 rng md  in
                FStar_Syntax_Syntax.as_arg uu____2627  in
              [uu____2626]  in
            uu____2621 :: uu____2623  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____2620
           in
        uu____2619 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____2642 =
          let uu____2643 =
            let uu____2644 =
              let uu____2645 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____2645  in
            let uu____2646 =
              let uu____2649 =
                let uu____2650 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____2650  in
              [uu____2649]  in
            uu____2644 :: uu____2646  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____2643
           in
        uu____2642 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___56_2653 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___56_2653.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___56_2653.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2666 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2666 with
    | (hd1,args) ->
        let uu____2705 =
          let uu____2718 =
            let uu____2719 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2719.FStar_Syntax_Syntax.n  in
          (uu____2718, args)  in
        (match uu____2705 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2734)::(md,uu____2736)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2771 = FStar_Syntax_Embeddings.unembed e_term t2  in
             FStar_Util.bind_opt uu____2771
               (fun t3  ->
                  let uu____2777 =
                    let uu____2782 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed uu____2782 md  in
                  FStar_Util.bind_opt uu____2777
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_63  -> FStar_Pervasives_Native.Some _0_63)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2801)::(post,uu____2803)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2838 = FStar_Syntax_Embeddings.unembed e_term pre  in
             FStar_Util.bind_opt uu____2838
               (fun pre1  ->
                  let uu____2844 =
                    FStar_Syntax_Embeddings.unembed e_term post  in
                  FStar_Util.bind_opt uu____2844
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_65  -> FStar_Pervasives_Native.Some _0_65)
               FStar_Reflection_Data.C_Unknown
         | uu____2868 ->
             (if w
              then
                (let uu____2882 =
                   let uu____2887 =
                     let uu____2888 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____2888
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2887)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2882)
              else ();
              FStar_Pervasives_Native.None))
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
    let uu___57_2900 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___57_2900.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___57_2900.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2913 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2913 with
    | (hd1,args) ->
        let uu____2952 =
          let uu____2965 =
            let uu____2966 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2966.FStar_Syntax_Syntax.n  in
          (uu____2965, args)  in
        (match uu____2952 with
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
         | uu____3024 ->
             (if w
              then
                (let uu____3038 =
                   let uu____3043 =
                     let uu____3044 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____3044
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3043)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3038)
              else ();
              FStar_Pervasives_Native.None))
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
    let uu____3066 =
      let uu____3067 = FStar_Syntax_Subst.compress t  in
      uu____3067.FStar_Syntax_Syntax.n  in
    match uu____3066 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____3073 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____3073
    | uu____3074 ->
        (if w
         then
           (let uu____3076 =
              let uu____3081 =
                let uu____3082 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____3082
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3081)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3076)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt
  
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,ty,t) ->
        let uu____3097 =
          let uu____3098 =
            let uu____3099 =
              let uu____3100 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____3100  in
            let uu____3101 =
              let uu____3104 =
                let uu____3105 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____3105  in
              let uu____3106 =
                let uu____3109 =
                  let uu____3110 =
                    FStar_Syntax_Embeddings.embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3110  in
                let uu____3111 =
                  let uu____3114 =
                    let uu____3115 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3115  in
                  [uu____3114]  in
                uu____3109 :: uu____3111  in
              uu____3104 :: uu____3106  in
            uu____3099 :: uu____3101  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____3098
           in
        uu____3097 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3120 =
          let uu____3121 =
            let uu____3122 =
              let uu____3123 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3123  in
            let uu____3126 =
              let uu____3129 =
                let uu____3130 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____3130  in
              [uu____3129]  in
            uu____3122 :: uu____3126  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____3121
           in
        uu____3120 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3145 =
          let uu____3146 =
            let uu____3147 =
              let uu____3148 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3148  in
            let uu____3151 =
              let uu____3154 =
                let uu____3155 =
                  FStar_Syntax_Embeddings.embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____3155  in
              let uu____3158 =
                let uu____3161 =
                  let uu____3162 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____3162  in
                let uu____3163 =
                  let uu____3166 =
                    let uu____3167 =
                      let uu____3168 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      FStar_Syntax_Embeddings.embed uu____3168 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____3167  in
                  [uu____3166]  in
                uu____3161 :: uu____3163  in
              uu____3154 :: uu____3158  in
            uu____3147 :: uu____3151  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____3146
           in
        uu____3145 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___58_3183 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___58_3183.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___58_3183.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3196 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3196 with
    | (hd1,args) ->
        let uu____3235 =
          let uu____3248 =
            let uu____3249 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3249.FStar_Syntax_Syntax.n  in
          (uu____3248, args)  in
        (match uu____3235 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3264)::(bs,uu____3266)::(t2,uu____3268)::(dcs,uu____3270)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3325 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____3325
               (fun nm1  ->
                  let uu____3339 =
                    FStar_Syntax_Embeddings.unembed e_binders bs  in
                  FStar_Util.bind_opt uu____3339
                    (fun bs1  ->
                       let uu____3353 =
                         FStar_Syntax_Embeddings.unembed e_term t2  in
                       FStar_Util.bind_opt uu____3353
                         (fun t3  ->
                            let uu____3359 =
                              let uu____3366 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_string_list
                                 in
                              FStar_Syntax_Embeddings.unembed uu____3366 dcs
                               in
                            FStar_Util.bind_opt uu____3359
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_Pervasives_Native.Some _0_66)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____3401)::(fvar1,uu____3403)::(ty,uu____3405)::(t2,uu____3407)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3462 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_bool
                 r
                in
             FStar_Util.bind_opt uu____3462
               (fun r1  ->
                  let uu____3468 = FStar_Syntax_Embeddings.unembed e_fv fvar1
                     in
                  FStar_Util.bind_opt uu____3468
                    (fun fvar2  ->
                       let uu____3474 =
                         FStar_Syntax_Embeddings.unembed e_term ty  in
                       FStar_Util.bind_opt uu____3474
                         (fun ty1  ->
                            let uu____3480 =
                              FStar_Syntax_Embeddings.unembed e_term t2  in
                            FStar_Util.bind_opt uu____3480
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_Pervasives_Native.Some _0_67)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3502 ->
             (if w
              then
                (let uu____3516 =
                   let uu____3521 =
                     let uu____3522 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____3522
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3521)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3516)
              else ();
              FStar_Pervasives_Native.None))
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
          let uu____3535 =
            let uu____3536 =
              let uu____3537 =
                let uu____3538 =
                  let uu____3539 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____3539  in
                FStar_Syntax_Syntax.as_arg uu____3538  in
              [uu____3537]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____3536
             in
          uu____3535 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____3544 =
            let uu____3545 =
              let uu____3546 =
                let uu____3547 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____3547  in
              let uu____3548 =
                let uu____3551 =
                  let uu____3552 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____3552  in
                [uu____3551]  in
              uu____3546 :: uu____3548  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____3545
             in
          uu____3544 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___59_3555 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___59_3555.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___59_3555.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3568 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3568 with
    | (hd1,args) ->
        let uu____3607 =
          let uu____3620 =
            let uu____3621 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3621.FStar_Syntax_Syntax.n  in
          (uu____3620, args)  in
        (match uu____3607 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____3651)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____3676 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____3676
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_68  -> FStar_Pervasives_Native.Some _0_68)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____3685)::(e2,uu____3687)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____3722 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____3722
               (fun e11  ->
                  let uu____3728 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____3728
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_69  -> FStar_Pervasives_Native.Some _0_69)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____3735 ->
             (if w
              then
                (let uu____3749 =
                   let uu____3754 =
                     let uu____3755 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____3755
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3754)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3749)
              else ();
              FStar_Pervasives_Native.None))
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
    let uu____3767 =
      let uu____3768 =
        let uu____3769 =
          let uu____3770 =
            let uu____3771 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____3771
             in
          FStar_Syntax_Syntax.as_arg uu____3770  in
        [uu____3769]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____3768
       in
    uu____3767 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3778 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____3778 with
    | (bv,aq) ->
        let uu____3785 =
          let uu____3786 =
            let uu____3787 =
              let uu____3788 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____3788  in
            let uu____3789 =
              let uu____3792 =
                let uu____3793 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____3793  in
              [uu____3792]  in
            uu____3787 :: uu____3789  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____3786
           in
        uu____3785 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3800 =
      let uu____3801 =
        let uu____3802 =
          let uu____3803 =
            let uu____3804 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____3809 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____3804
              i.FStar_Syntax_Syntax.rng uu____3809
             in
          FStar_Syntax_Syntax.as_arg uu____3803  in
        [uu____3802]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____3801
       in
    uu____3800 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3820 =
      let uu____3821 =
        let uu____3822 =
          let uu____3823 =
            let uu____3824 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____3824
             in
          FStar_Syntax_Syntax.as_arg uu____3823  in
        [uu____3822]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____3821
       in
    uu____3820 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3834 =
      let uu____3835 =
        let uu____3836 =
          let uu____3837 =
            let uu____3838 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____3838
             in
          FStar_Syntax_Syntax.as_arg uu____3837  in
        [uu____3836]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____3835
       in
    uu____3834 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  