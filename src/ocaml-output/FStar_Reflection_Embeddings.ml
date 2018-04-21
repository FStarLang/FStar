open Prims
let e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____29 =
      let uu____30 = FStar_Syntax_Subst.compress t  in
      uu____30.FStar_Syntax_Syntax.n  in
    match uu____29 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____36 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____36
    | uu____37 ->
        (if w
         then
           (let uu____39 =
              let uu____44 =
                let uu____45 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____45  in
              (FStar_Errors.Warning_NotEmbedded, uu____44)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____39)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_bv unembed_bv
    FStar_Reflection_Data.fstar_refl_bv
  
let e_binder : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding =
  let embed_binder rng b =
    FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng)
     in
  let unembed_binder w t =
    let uu____75 =
      let uu____76 = FStar_Syntax_Subst.compress t  in
      uu____76.FStar_Syntax_Syntax.n  in
    match uu____75 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____82 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____82
    | uu____83 ->
        (if w
         then
           (let uu____85 =
              let uu____90 =
                let uu____91 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____91  in
              (FStar_Errors.Warning_NotEmbedded, uu____90)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____85)
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
          let uu____138 = f x  in
          FStar_Util.bind_opt uu____138
            (fun x1  ->
               let uu____146 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____146
                 (fun xs1  -> FStar_Pervasives_Native.Some (x1 :: xs1)))
  
let e_term_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding
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
        let uu____210 =
          mapM_opt
            (fun uu____227  ->
               match uu____227 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____250 = unembed_term w e  in
                      FStar_Util.bind_opt uu____250
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1))))) aq1
           in
        FStar_Util.bind_opt uu____210
          (fun s  ->
             let uu____262 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____262)
         in
      let uu____263 =
        let uu____264 = FStar_Syntax_Subst.compress t  in
        uu____264.FStar_Syntax_Syntax.n  in
      match uu____263 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____275 ->
          (if w
           then
             (let uu____277 =
                let uu____282 =
                  let uu____283 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____283  in
                (FStar_Errors.Warning_NotEmbedded, uu____282)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____277)
           else ();
           FStar_Pervasives_Native.None)
       in
    FStar_Syntax_Embeddings.mk_emb embed_term unembed_term
      FStar_Syntax_Syntax.t_term
  
let e_term : FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding =
  e_term_aq [] 
let e_aqualv : FStar_Reflection_Data.aqualv FStar_Syntax_Embeddings.embedding
  =
  let embed_aqualv rng q =
    let r =
      match q with
      | FStar_Reflection_Data.Q_Explicit  ->
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Q_Implicit  ->
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.t
       in
    let uu___53_309 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___53_309.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___53_309.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____326 = FStar_Syntax_Util.head_and_args t1  in
    match uu____326 with
    | (hd1,args) ->
        let uu____365 =
          let uu____378 =
            let uu____379 = FStar_Syntax_Util.un_uinst hd1  in
            uu____379.FStar_Syntax_Syntax.n  in
          (uu____378, args)  in
        (match uu____365 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____422 ->
             (if w
              then
                (let uu____436 =
                   let uu____441 =
                     let uu____442 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____442
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____441)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____436)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_aqualv unembed_aqualv
    FStar_Reflection_Data.fstar_refl_aqualv
  
let e_binders :
  FStar_Syntax_Syntax.binder Prims.list FStar_Syntax_Embeddings.embedding =
  FStar_Syntax_Embeddings.e_list e_binder 
let e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings.embedding =
  let embed_fv rng fv =
    FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
     in
  let unembed_fv w t =
    let uu____476 =
      let uu____477 = FStar_Syntax_Subst.compress t  in
      uu____477.FStar_Syntax_Syntax.n  in
    match uu____476 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____483 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____483
    | uu____484 ->
        (if w
         then
           (let uu____486 =
              let uu____491 =
                let uu____492 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____492  in
              (FStar_Errors.Warning_NotEmbedded, uu____491)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____486)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_fv unembed_fv
    FStar_Reflection_Data.fstar_refl_fv
  
let e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding =
  let embed_comp rng c =
    FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng)
     in
  let unembed_comp w t =
    let uu____522 =
      let uu____523 = FStar_Syntax_Subst.compress t  in
      uu____523.FStar_Syntax_Syntax.n  in
    match uu____522 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____529 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____529
    | uu____530 ->
        (if w
         then
           (let uu____532 =
              let uu____537 =
                let uu____538 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____538  in
              (FStar_Errors.Warning_NotEmbedded, uu____537)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____532)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_comp unembed_comp
    FStar_Reflection_Data.fstar_refl_comp
  
let e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng)
     in
  let unembed_env w t =
    let uu____568 =
      let uu____569 = FStar_Syntax_Subst.compress t  in
      uu____569.FStar_Syntax_Syntax.n  in
    match uu____568 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____575 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____575
    | uu____576 ->
        (if w
         then
           (let uu____578 =
              let uu____583 =
                let uu____584 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____584  in
              (FStar_Errors.Warning_NotEmbedded, uu____583)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____578)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_env unembed_env
    FStar_Reflection_Data.fstar_refl_env
  
let e_const : FStar_Reflection_Data.vconst FStar_Syntax_Embeddings.embedding
  =
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
          let uu____601 =
            let uu____606 =
              let uu____607 =
                let uu____608 =
                  let uu____609 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____609  in
                FStar_Syntax_Syntax.as_arg uu____608  in
              [uu____607]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____606
             in
          uu____601 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____613 =
            let uu____618 =
              let uu____619 =
                let uu____620 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____620  in
              [uu____619]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____618
             in
          uu____613 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___54_623 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___54_623.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___54_623.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____640 = FStar_Syntax_Util.head_and_args t1  in
    match uu____640 with
    | (hd1,args) ->
        let uu____679 =
          let uu____692 =
            let uu____693 = FStar_Syntax_Util.un_uinst hd1  in
            uu____693.FStar_Syntax_Syntax.n  in
          (uu____692, args)  in
        (match uu____679 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____753)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____778 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____778
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____787)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____812 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____812
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                    (FStar_Reflection_Data.C_String s1))
         | uu____819 ->
             (if w
              then
                (let uu____833 =
                   let uu____838 =
                     let uu____839 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____839
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____838)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____833)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst
  
let rec e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding =
  fun uu____847  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____860 =
            let uu____865 =
              let uu____866 =
                let uu____867 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____867  in
              [uu____866]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____865
             in
          uu____860 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____876 =
            let uu____881 =
              let uu____882 =
                let uu____883 = FStar_Syntax_Embeddings.embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____883  in
              let uu____884 =
                let uu____887 =
                  let uu____888 =
                    let uu____889 =
                      let uu____894 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____894  in
                    FStar_Syntax_Embeddings.embed uu____889 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____888  in
                [uu____887]  in
              uu____882 :: uu____884  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____881
             in
          uu____876 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____902 =
            let uu____907 =
              let uu____908 =
                let uu____909 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____909  in
              [uu____908]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____907
             in
          uu____902 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____913 =
            let uu____918 =
              let uu____919 =
                let uu____920 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____920  in
              [uu____919]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____918
             in
          uu____913 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____925 =
            let uu____930 =
              let uu____931 =
                let uu____932 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____932  in
              let uu____933 =
                let uu____936 =
                  let uu____937 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____937  in
                [uu____936]  in
              uu____931 :: uu____933  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____930
             in
          uu____925 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____956 = FStar_Syntax_Util.head_and_args t1  in
      match uu____956 with
      | (hd1,args) ->
          let uu____995 =
            let uu____1008 =
              let uu____1009 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1009.FStar_Syntax_Syntax.n  in
            (uu____1008, args)  in
          (match uu____995 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1024)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1049 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____1049
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1058)::(ps,uu____1060)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1095 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____1095
                 (fun f1  ->
                    let uu____1101 =
                      let uu____1106 =
                        let uu____1111 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1111  in
                      FStar_Syntax_Embeddings.unembed uu____1106 ps  in
                    FStar_Util.bind_opt uu____1101
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1128)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1153 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1153
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1162)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1187 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1187
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1196)::(t2,uu____1198)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1233 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1233
                 (fun bv1  ->
                    let uu____1239 =
                      FStar_Syntax_Embeddings.unembed e_term t2  in
                    FStar_Util.bind_opt uu____1239
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1246 ->
               (if w
                then
                  (let uu____1260 =
                     let uu____1265 =
                       let uu____1266 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1266
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1265)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1260)
                else ();
                FStar_Pervasives_Native.None))
       in
    FStar_Syntax_Embeddings.mk_emb embed_pattern unembed_pattern
      FStar_Reflection_Data.fstar_refl_pattern
  
let e_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding =
  e_pattern' () 
let e_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding
  = FStar_Syntax_Embeddings.e_tuple2 e_pattern e_term 
let e_argv :
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding
  = FStar_Syntax_Embeddings.e_tuple2 e_term e_aqualv 
let e_branch_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding
  =
  fun aq  ->
    let uu____1293 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1293
  
let e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding
  =
  fun aq  ->
    let uu____1307 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1307 e_aqualv
  
let e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1329 =
            let uu____1334 =
              let uu____1335 =
                let uu____1336 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1336  in
              [uu____1335]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1334
             in
          uu____1329 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1340 =
            let uu____1345 =
              let uu____1346 =
                let uu____1347 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1347  in
              [uu____1346]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1345
             in
          uu____1340 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1351 =
            let uu____1356 =
              let uu____1357 =
                let uu____1358 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1358  in
              [uu____1357]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1356
             in
          uu____1351 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1363 =
            let uu____1368 =
              let uu____1369 =
                let uu____1370 =
                  let uu____1371 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1371 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1370  in
              let uu____1374 =
                let uu____1377 =
                  let uu____1378 =
                    let uu____1379 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1379 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1378  in
                [uu____1377]  in
              uu____1369 :: uu____1374  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1368
             in
          uu____1363 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1394 =
            let uu____1399 =
              let uu____1400 =
                let uu____1401 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1401  in
              let uu____1402 =
                let uu____1405 =
                  let uu____1406 =
                    let uu____1407 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1407 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1406  in
                [uu____1405]  in
              uu____1400 :: uu____1402  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1399
             in
          uu____1394 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1414 =
            let uu____1419 =
              let uu____1420 =
                let uu____1421 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1421  in
              let uu____1422 =
                let uu____1425 =
                  let uu____1426 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1426  in
                [uu____1425]  in
              uu____1420 :: uu____1422  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1419
             in
          uu____1414 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1430 =
            let uu____1435 =
              let uu____1436 =
                let uu____1437 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1437  in
              [uu____1436]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____1435
             in
          uu____1430 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1442 =
            let uu____1447 =
              let uu____1448 =
                let uu____1449 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1449  in
              let uu____1450 =
                let uu____1453 =
                  let uu____1454 =
                    let uu____1455 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1455 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1454  in
                [uu____1453]  in
              uu____1448 :: uu____1450  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____1447
             in
          uu____1442 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1461 =
            let uu____1466 =
              let uu____1467 =
                let uu____1468 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____1468  in
              [uu____1467]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____1466
             in
          uu____1461 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1473 =
            let uu____1478 =
              let uu____1479 =
                let uu____1480 =
                  FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int
                    rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____1480  in
              let uu____1481 =
                let uu____1484 =
                  let uu____1485 =
                    let uu____1486 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1486 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1485  in
                [uu____1484]  in
              uu____1479 :: uu____1481  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____1478
             in
          uu____1473 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1495 =
            let uu____1500 =
              let uu____1501 =
                let uu____1502 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1502  in
              let uu____1503 =
                let uu____1506 =
                  let uu____1507 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____1507  in
                let uu____1508 =
                  let uu____1511 =
                    let uu____1512 =
                      let uu____1513 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____1513 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____1512  in
                  let uu____1516 =
                    let uu____1519 =
                      let uu____1520 =
                        let uu____1521 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____1521 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____1520  in
                    [uu____1519]  in
                  uu____1511 :: uu____1516  in
                uu____1506 :: uu____1508  in
              uu____1501 :: uu____1503  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____1500
             in
          uu____1495 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1532 =
            let uu____1537 =
              let uu____1538 =
                let uu____1539 =
                  let uu____1540 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1540 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____1539  in
              let uu____1543 =
                let uu____1546 =
                  let uu____1547 =
                    let uu____1548 =
                      let uu____1557 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____1557  in
                    FStar_Syntax_Embeddings.embed uu____1548 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____1547  in
                [uu____1546]  in
              uu____1538 :: uu____1543  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____1537
             in
          uu____1532 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____1583 =
            let uu____1588 =
              let uu____1589 =
                let uu____1590 =
                  let uu____1591 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1591 rng e  in
                FStar_Syntax_Syntax.as_arg uu____1590  in
              let uu____1594 =
                let uu____1597 =
                  let uu____1598 =
                    let uu____1599 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1599 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1598  in
                let uu____1602 =
                  let uu____1605 =
                    let uu____1606 =
                      let uu____1607 =
                        let uu____1612 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____1612  in
                      FStar_Syntax_Embeddings.embed uu____1607 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____1606  in
                  [uu____1605]  in
                uu____1597 :: uu____1602  in
              uu____1589 :: uu____1594  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____1588
             in
          uu____1583 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____1626 =
            let uu____1631 =
              let uu____1632 =
                let uu____1633 =
                  let uu____1634 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1634 rng e  in
                FStar_Syntax_Syntax.as_arg uu____1633  in
              let uu____1637 =
                let uu____1640 =
                  let uu____1641 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1641  in
                let uu____1642 =
                  let uu____1645 =
                    let uu____1646 =
                      let uu____1647 =
                        let uu____1652 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____1652  in
                      FStar_Syntax_Embeddings.embed uu____1647 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____1646  in
                  [uu____1645]  in
                uu____1640 :: uu____1642  in
              uu____1632 :: uu____1637  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____1631
             in
          uu____1626 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___55_1659 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___55_1659.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___55_1659.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____1675 = FStar_Syntax_Util.head_and_args t  in
      match uu____1675 with
      | (hd1,args) ->
          let uu____1714 =
            let uu____1727 =
              let uu____1728 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1728.FStar_Syntax_Syntax.n  in
            (uu____1727, args)  in
          (match uu____1714 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1743)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____1768 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____1768
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1777)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____1802 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____1802
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1811)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____1836 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____1836
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____1845)::(r,uu____1847)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____1882 = FStar_Syntax_Embeddings.unembed e_term l  in
               FStar_Util.bind_opt uu____1882
                 (fun l1  ->
                    let uu____1888 = FStar_Syntax_Embeddings.unembed e_argv r
                       in
                    FStar_Util.bind_opt uu____1888
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1917)::(t1,uu____1919)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____1954 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____1954
                 (fun b1  ->
                    let uu____1960 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____1960
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1969)::(t1,uu____1971)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____2006 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____2006
                 (fun b1  ->
                    let uu____2012 =
                      FStar_Syntax_Embeddings.unembed e_comp t1  in
                    FStar_Util.bind_opt uu____2012
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2021)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____2046 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____2046
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2055)::(t1,uu____2057)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____2092 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____2092
                 (fun b1  ->
                    let uu____2098 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2098
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2107)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____2132 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____2132
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____2141)::(t1,uu____2143)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____2178 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____2178
                 (fun u1  ->
                    let uu____2184 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2184
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                           (FStar_Reflection_Data.Tv_Uvar (u1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____2193)::(b,uu____2195)::(t1,uu____2197)::(t2,uu____2199)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____2254 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____2254
                 (fun r1  ->
                    let uu____2260 = FStar_Syntax_Embeddings.unembed e_bv b
                       in
                    FStar_Util.bind_opt uu____2260
                      (fun b1  ->
                         let uu____2266 =
                           FStar_Syntax_Embeddings.unembed e_term t1  in
                         FStar_Util.bind_opt uu____2266
                           (fun t11  ->
                              let uu____2272 =
                                FStar_Syntax_Embeddings.unembed e_term t2  in
                              FStar_Util.bind_opt uu____2272
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_34  ->
                                        FStar_Pervasives_Native.Some _0_34)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____2281)::(brs,uu____2283)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____2318 = FStar_Syntax_Embeddings.unembed e_term t1  in
               FStar_Util.bind_opt uu____2318
                 (fun t2  ->
                    let uu____2324 =
                      let uu____2333 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed uu____2333 brs  in
                    FStar_Util.bind_opt uu____2324
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2376)::(t1,uu____2378)::(tacopt,uu____2380)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____2425 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2425
                 (fun e1  ->
                    let uu____2431 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2431
                      (fun t2  ->
                         let uu____2437 =
                           let uu____2442 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2442 tacopt
                            in
                         FStar_Util.bind_opt uu____2437
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_36  ->
                                   FStar_Pervasives_Native.Some _0_36)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2461)::(c,uu____2463)::(tacopt,uu____2465)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____2510 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2510
                 (fun e1  ->
                    let uu____2516 = FStar_Syntax_Embeddings.unembed e_comp c
                       in
                    FStar_Util.bind_opt uu____2516
                      (fun c1  ->
                         let uu____2522 =
                           let uu____2527 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2527 tacopt
                            in
                         FStar_Util.bind_opt uu____2522
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
           | uu____2561 ->
               (if w
                then
                  (let uu____2575 =
                     let uu____2580 =
                       let uu____2581 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____2581
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2580)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____2575)
                else ();
                FStar_Pervasives_Native.None))
       in
    FStar_Syntax_Embeddings.mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view
  
let e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding =
  e_term_view_aq [] 
let e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding =
  let embed_bv_view rng bvv =
    let uu____2606 =
      let uu____2611 =
        let uu____2612 =
          let uu____2613 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____2613  in
        let uu____2614 =
          let uu____2617 =
            let uu____2618 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____2618  in
          let uu____2619 =
            let uu____2622 =
              let uu____2623 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____2623  in
            [uu____2622]  in
          uu____2617 :: uu____2619  in
        uu____2612 :: uu____2614  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____2611
       in
    uu____2606 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2642 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2642 with
    | (hd1,args) ->
        let uu____2681 =
          let uu____2694 =
            let uu____2695 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2695.FStar_Syntax_Syntax.n  in
          (uu____2694, args)  in
        (match uu____2681 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2710)::(idx,uu____2712)::(s,uu____2714)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2759 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____2759
               (fun nm1  ->
                  let uu____2765 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____2765
                    (fun idx1  ->
                       let uu____2771 =
                         FStar_Syntax_Embeddings.unembed e_term s  in
                       FStar_Util.bind_opt uu____2771
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_39  ->
                                 FStar_Pervasives_Native.Some _0_39)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2778 ->
             (if w
              then
                (let uu____2792 =
                   let uu____2797 =
                     let uu____2798 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____2798
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2797)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2792)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view
  
let e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____2819 =
          let uu____2824 =
            let uu____2825 =
              let uu____2826 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____2826  in
            let uu____2827 =
              let uu____2830 =
                let uu____2831 =
                  let uu____2832 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____2832 rng md  in
                FStar_Syntax_Syntax.as_arg uu____2831  in
              [uu____2830]  in
            uu____2825 :: uu____2827  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____2824
           in
        uu____2819 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____2846 =
          let uu____2851 =
            let uu____2852 =
              let uu____2853 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____2853  in
            let uu____2854 =
              let uu____2857 =
                let uu____2858 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____2858  in
              [uu____2857]  in
            uu____2852 :: uu____2854  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____2851
           in
        uu____2846 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___56_2861 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___56_2861.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___56_2861.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2878 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2878 with
    | (hd1,args) ->
        let uu____2917 =
          let uu____2930 =
            let uu____2931 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2931.FStar_Syntax_Syntax.n  in
          (uu____2930, args)  in
        (match uu____2917 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2946)::(md,uu____2948)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2983 = FStar_Syntax_Embeddings.unembed e_term t2  in
             FStar_Util.bind_opt uu____2983
               (fun t3  ->
                  let uu____2989 =
                    let uu____2994 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed uu____2994 md  in
                  FStar_Util.bind_opt uu____2989
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____3013)::(post,uu____3015)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____3050 = FStar_Syntax_Embeddings.unembed e_term pre  in
             FStar_Util.bind_opt uu____3050
               (fun pre1  ->
                  let uu____3056 =
                    FStar_Syntax_Embeddings.unembed e_term post  in
                  FStar_Util.bind_opt uu____3056
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
         | uu____3080 ->
             (if w
              then
                (let uu____3094 =
                   let uu____3099 =
                     let uu____3100 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____3100
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3099)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3094)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_comp_view unembed_comp_view
    FStar_Reflection_Data.fstar_refl_comp_view
  
let e_order : FStar_Order.order FStar_Syntax_Embeddings.embedding =
  let embed_order rng o =
    let r =
      match o with
      | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
      | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
      | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt  in
    let uu___57_3116 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___57_3116.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___57_3116.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3133 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3133 with
    | (hd1,args) ->
        let uu____3172 =
          let uu____3185 =
            let uu____3186 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3186.FStar_Syntax_Syntax.n  in
          (uu____3185, args)  in
        (match uu____3172 with
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
         | uu____3244 ->
             (if w
              then
                (let uu____3258 =
                   let uu____3263 =
                     let uu____3264 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____3264
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3263)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3258)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_order unembed_order
    FStar_Syntax_Syntax.t_order
  
let e_sigelt : FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings.embedding =
  let embed_sigelt rng se =
    FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng)
     in
  let unembed_sigelt w t =
    let uu____3294 =
      let uu____3295 = FStar_Syntax_Subst.compress t  in
      uu____3295.FStar_Syntax_Syntax.n  in
    match uu____3294 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____3301 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____3301
    | uu____3302 ->
        (if w
         then
           (let uu____3304 =
              let uu____3309 =
                let uu____3310 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____3310
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3309)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3304)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt
  
let e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,ty,t) ->
        let uu____3329 =
          let uu____3334 =
            let uu____3335 =
              let uu____3336 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____3336  in
            let uu____3337 =
              let uu____3340 =
                let uu____3341 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____3341  in
              let uu____3342 =
                let uu____3345 =
                  let uu____3346 =
                    FStar_Syntax_Embeddings.embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3346  in
                let uu____3347 =
                  let uu____3350 =
                    let uu____3351 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3351  in
                  [uu____3350]  in
                uu____3345 :: uu____3347  in
              uu____3340 :: uu____3342  in
            uu____3335 :: uu____3337  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____3334
           in
        uu____3329 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3356 =
          let uu____3361 =
            let uu____3362 =
              let uu____3363 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3363  in
            let uu____3366 =
              let uu____3369 =
                let uu____3370 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____3370  in
              [uu____3369]  in
            uu____3362 :: uu____3366  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____3361
           in
        uu____3356 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3385 =
          let uu____3390 =
            let uu____3391 =
              let uu____3392 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3392  in
            let uu____3395 =
              let uu____3398 =
                let uu____3399 =
                  FStar_Syntax_Embeddings.embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____3399  in
              let uu____3402 =
                let uu____3405 =
                  let uu____3406 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____3406  in
                let uu____3407 =
                  let uu____3410 =
                    let uu____3411 =
                      let uu____3412 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      FStar_Syntax_Embeddings.embed uu____3412 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____3411  in
                  [uu____3410]  in
                uu____3405 :: uu____3407  in
              uu____3398 :: uu____3402  in
            uu____3391 :: uu____3395  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____3390
           in
        uu____3385 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___58_3427 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___58_3427.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___58_3427.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3444 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3444 with
    | (hd1,args) ->
        let uu____3483 =
          let uu____3496 =
            let uu____3497 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3497.FStar_Syntax_Syntax.n  in
          (uu____3496, args)  in
        (match uu____3483 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3512)::(bs,uu____3514)::(t2,uu____3516)::(dcs,uu____3518)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3573 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____3573
               (fun nm1  ->
                  let uu____3587 =
                    FStar_Syntax_Embeddings.unembed e_binders bs  in
                  FStar_Util.bind_opt uu____3587
                    (fun bs1  ->
                       let uu____3601 =
                         FStar_Syntax_Embeddings.unembed e_term t2  in
                       FStar_Util.bind_opt uu____3601
                         (fun t3  ->
                            let uu____3607 =
                              let uu____3614 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_string_list
                                 in
                              FStar_Syntax_Embeddings.unembed uu____3614 dcs
                               in
                            FStar_Util.bind_opt uu____3607
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____3649)::(fvar1,uu____3651)::(ty,uu____3653)::(t2,uu____3655)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3710 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_bool
                 r
                in
             FStar_Util.bind_opt uu____3710
               (fun r1  ->
                  let uu____3716 = FStar_Syntax_Embeddings.unembed e_fv fvar1
                     in
                  FStar_Util.bind_opt uu____3716
                    (fun fvar2  ->
                       let uu____3722 =
                         FStar_Syntax_Embeddings.unembed e_term ty  in
                       FStar_Util.bind_opt uu____3722
                         (fun ty1  ->
                            let uu____3728 =
                              FStar_Syntax_Embeddings.unembed e_term t2  in
                            FStar_Util.bind_opt uu____3728
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
         | uu____3750 ->
             (if w
              then
                (let uu____3764 =
                   let uu____3769 =
                     let uu____3770 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____3770
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3769)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3764)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_Data.fstar_refl_sigelt_view
  
let e_exp : FStar_Reflection_Data.exp FStar_Syntax_Embeddings.embedding =
  let rec embed_exp rng e =
    let r =
      match e with
      | FStar_Reflection_Data.Unit  ->
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Var i ->
          let uu____3787 =
            let uu____3792 =
              let uu____3793 =
                let uu____3794 =
                  let uu____3795 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____3795  in
                FStar_Syntax_Syntax.as_arg uu____3794  in
              [uu____3793]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____3792
             in
          uu____3787 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____3800 =
            let uu____3805 =
              let uu____3806 =
                let uu____3807 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____3807  in
              let uu____3808 =
                let uu____3811 =
                  let uu____3812 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____3812  in
                [uu____3811]  in
              uu____3806 :: uu____3808  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____3805
             in
          uu____3800 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___59_3815 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___59_3815.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___59_3815.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3832 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3832 with
    | (hd1,args) ->
        let uu____3871 =
          let uu____3884 =
            let uu____3885 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3885.FStar_Syntax_Syntax.n  in
          (uu____3884, args)  in
        (match uu____3871 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____3915)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____3940 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____3940
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____3949)::(e2,uu____3951)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____3986 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____3986
               (fun e11  ->
                  let uu____3992 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____3992
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____3999 ->
             (if w
              then
                (let uu____4013 =
                   let uu____4018 =
                     let uu____4019 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____4019
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4018)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4013)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_exp unembed_exp
    FStar_Reflection_Data.fstar_refl_exp
  
let e_binder_view :
  (FStar_Syntax_Syntax.bv,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding
  = FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv 
let unfold_lazy_bv : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term
  =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4033 =
      let uu____4038 =
        let uu____4039 =
          let uu____4040 =
            let uu____4041 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____4041
             in
          FStar_Syntax_Syntax.as_arg uu____4040  in
        [uu____4039]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____4038
       in
    uu____4033 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4050 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____4050 with
    | (bv,aq) ->
        let uu____4057 =
          let uu____4062 =
            let uu____4063 =
              let uu____4064 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____4064  in
            let uu____4065 =
              let uu____4068 =
                let uu____4069 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____4069  in
              [uu____4068]  in
            uu____4063 :: uu____4065  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____4062
           in
        uu____4057 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4078 =
      let uu____4083 =
        let uu____4084 =
          let uu____4085 =
            let uu____4086 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____4091 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____4086
              i.FStar_Syntax_Syntax.rng uu____4091
             in
          FStar_Syntax_Syntax.as_arg uu____4085  in
        [uu____4084]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____4083
       in
    uu____4078 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4104 =
      let uu____4109 =
        let uu____4110 =
          let uu____4111 =
            let uu____4112 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____4112
             in
          FStar_Syntax_Syntax.as_arg uu____4111  in
        [uu____4110]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____4109
       in
    uu____4104 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term =
  fun i  -> FStar_Syntax_Util.exp_unit 
let unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4126 =
      let uu____4131 =
        let uu____4132 =
          let uu____4133 =
            let uu____4134 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____4134
             in
          FStar_Syntax_Syntax.as_arg uu____4133  in
        [uu____4132]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____4131
       in
    uu____4126 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  