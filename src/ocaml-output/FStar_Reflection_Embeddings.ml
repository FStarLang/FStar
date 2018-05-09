open Prims
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
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
  
let (e_binder : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding)
  =
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
    let uu___77_309 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___77_309.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___77_309.FStar_Syntax_Syntax.vars)
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
  
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_list e_binder 
let (e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings.embedding) =
  let embed_fv rng fv =
    FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
     in
  let unembed_fv w t =
    let uu____474 =
      let uu____475 = FStar_Syntax_Subst.compress t  in
      uu____475.FStar_Syntax_Syntax.n  in
    match uu____474 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____481 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____481
    | uu____482 ->
        (if w
         then
           (let uu____484 =
              let uu____489 =
                let uu____490 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____490  in
              (FStar_Errors.Warning_NotEmbedded, uu____489)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____484)
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
    let uu____520 =
      let uu____521 = FStar_Syntax_Subst.compress t  in
      uu____521.FStar_Syntax_Syntax.n  in
    match uu____520 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____527 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____527
    | uu____528 ->
        (if w
         then
           (let uu____530 =
              let uu____535 =
                let uu____536 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____536  in
              (FStar_Errors.Warning_NotEmbedded, uu____535)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____530)
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
    let uu____566 =
      let uu____567 = FStar_Syntax_Subst.compress t  in
      uu____567.FStar_Syntax_Syntax.n  in
    match uu____566 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____573 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____573
    | uu____574 ->
        (if w
         then
           (let uu____576 =
              let uu____581 =
                let uu____582 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____582  in
              (FStar_Errors.Warning_NotEmbedded, uu____581)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____576)
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
          let uu____599 =
            let uu____604 =
              let uu____605 =
                let uu____606 =
                  let uu____607 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____607  in
                FStar_Syntax_Syntax.as_arg uu____606  in
              [uu____605]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____604
             in
          uu____599 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____611 =
            let uu____616 =
              let uu____617 =
                let uu____618 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____618  in
              [uu____617]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____616
             in
          uu____611 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___78_621 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___78_621.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___78_621.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____638 = FStar_Syntax_Util.head_and_args t1  in
    match uu____638 with
    | (hd1,args) ->
        let uu____677 =
          let uu____690 =
            let uu____691 = FStar_Syntax_Util.un_uinst hd1  in
            uu____691.FStar_Syntax_Syntax.n  in
          (uu____690, args)  in
        (match uu____677 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____751)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____776 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_int i
                in
             FStar_Util.bind_opt uu____776
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____785)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____810 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____810
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____817 ->
             (if w
              then
                (let uu____831 =
                   let uu____836 =
                     let uu____837 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____837
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____836)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____831)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____845  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____858 =
            let uu____863 =
              let uu____864 =
                let uu____865 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____865  in
              [uu____864]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____863
             in
          uu____858 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____874 =
            let uu____879 =
              let uu____880 =
                let uu____881 = FStar_Syntax_Embeddings.embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____881  in
              let uu____882 =
                let uu____885 =
                  let uu____886 =
                    let uu____887 =
                      let uu____892 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____892  in
                    FStar_Syntax_Embeddings.embed uu____887 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____886  in
                [uu____885]  in
              uu____880 :: uu____882  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____879
             in
          uu____874 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____900 =
            let uu____905 =
              let uu____906 =
                let uu____907 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____907  in
              [uu____906]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____905
             in
          uu____900 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____911 =
            let uu____916 =
              let uu____917 =
                let uu____918 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____918  in
              [uu____917]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____916
             in
          uu____911 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____923 =
            let uu____928 =
              let uu____929 =
                let uu____930 = FStar_Syntax_Embeddings.embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____930  in
              let uu____931 =
                let uu____934 =
                  let uu____935 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____935  in
                [uu____934]  in
              uu____929 :: uu____931  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____928
             in
          uu____923 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____954 = FStar_Syntax_Util.head_and_args t1  in
      match uu____954 with
      | (hd1,args) ->
          let uu____993 =
            let uu____1006 =
              let uu____1007 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1007.FStar_Syntax_Syntax.n  in
            (uu____1006, args)  in
          (match uu____993 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1022)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1047 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____1047
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1056)::(ps,uu____1058)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1093 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1093
                 (fun f1  ->
                    let uu____1099 =
                      let uu____1104 =
                        let uu____1109 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1109  in
                      FStar_Syntax_Embeddings.unembed' w uu____1104 ps  in
                    FStar_Util.bind_opt uu____1099
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1126)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1151 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1151
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1160)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1185 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1185
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1194)::(t2,uu____1196)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1231 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1231
                 (fun bv1  ->
                    let uu____1237 =
                      FStar_Syntax_Embeddings.unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1237
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1244 ->
               (if w
                then
                  (let uu____1258 =
                     let uu____1263 =
                       let uu____1264 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1264
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1263)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1258)
                else ();
                FStar_Pervasives_Native.None))
       in
    FStar_Syntax_Embeddings.mk_emb embed_pattern unembed_pattern
      FStar_Reflection_Data.fstar_refl_pattern
  
let (e_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  e_pattern' () 
let (e_branch :
  FStar_Reflection_Data.branch FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_pattern e_term 
let (e_argv : FStar_Reflection_Data.argv FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_term e_aqualv 
let (e_branch_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1283 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1283
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1297 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1297 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1319 =
            let uu____1324 =
              let uu____1325 =
                let uu____1326 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1326  in
              [uu____1325]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1324
             in
          uu____1319 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1330 =
            let uu____1335 =
              let uu____1336 =
                let uu____1337 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1337  in
              [uu____1336]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1335
             in
          uu____1330 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1341 =
            let uu____1346 =
              let uu____1347 =
                let uu____1348 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1348  in
              [uu____1347]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1346
             in
          uu____1341 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1353 =
            let uu____1358 =
              let uu____1359 =
                let uu____1360 =
                  let uu____1361 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1361 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1360  in
              let uu____1364 =
                let uu____1367 =
                  let uu____1368 =
                    let uu____1369 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1369 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1368  in
                [uu____1367]  in
              uu____1359 :: uu____1364  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1358
             in
          uu____1353 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1384 =
            let uu____1389 =
              let uu____1390 =
                let uu____1391 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1391  in
              let uu____1392 =
                let uu____1395 =
                  let uu____1396 =
                    let uu____1397 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1397 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1396  in
                [uu____1395]  in
              uu____1390 :: uu____1392  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1389
             in
          uu____1384 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1404 =
            let uu____1409 =
              let uu____1410 =
                let uu____1411 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1411  in
              let uu____1412 =
                let uu____1415 =
                  let uu____1416 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1416  in
                [uu____1415]  in
              uu____1410 :: uu____1412  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1409
             in
          uu____1404 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1420 =
            let uu____1425 =
              let uu____1426 =
                let uu____1427 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1427  in
              [uu____1426]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____1425
             in
          uu____1420 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1432 =
            let uu____1437 =
              let uu____1438 =
                let uu____1439 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1439  in
              let uu____1440 =
                let uu____1443 =
                  let uu____1444 =
                    let uu____1445 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1445 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1444  in
                [uu____1443]  in
              uu____1438 :: uu____1440  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____1437
             in
          uu____1432 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1451 =
            let uu____1456 =
              let uu____1457 =
                let uu____1458 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____1458  in
              [uu____1457]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____1456
             in
          uu____1451 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____1463 =
            let uu____1468 =
              let uu____1469 =
                let uu____1470 =
                  FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int
                    rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____1470  in
              let uu____1471 =
                let uu____1474 =
                  let uu____1475 =
                    let uu____1476 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1476 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1475  in
                [uu____1474]  in
              uu____1469 :: uu____1471  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____1468
             in
          uu____1463 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1485 =
            let uu____1490 =
              let uu____1491 =
                let uu____1492 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1492  in
              let uu____1493 =
                let uu____1496 =
                  let uu____1497 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____1497  in
                let uu____1498 =
                  let uu____1501 =
                    let uu____1502 =
                      let uu____1503 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____1503 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____1502  in
                  let uu____1506 =
                    let uu____1509 =
                      let uu____1510 =
                        let uu____1511 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____1511 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____1510  in
                    [uu____1509]  in
                  uu____1501 :: uu____1506  in
                uu____1496 :: uu____1498  in
              uu____1491 :: uu____1493  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____1490
             in
          uu____1485 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____1522 =
            let uu____1527 =
              let uu____1528 =
                let uu____1529 =
                  let uu____1530 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1530 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____1529  in
              let uu____1533 =
                let uu____1536 =
                  let uu____1537 =
                    let uu____1538 =
                      let uu____1547 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____1547  in
                    FStar_Syntax_Embeddings.embed uu____1538 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____1537  in
                [uu____1536]  in
              uu____1528 :: uu____1533  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____1527
             in
          uu____1522 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____1573 =
            let uu____1578 =
              let uu____1579 =
                let uu____1580 =
                  let uu____1581 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1581 rng e  in
                FStar_Syntax_Syntax.as_arg uu____1580  in
              let uu____1584 =
                let uu____1587 =
                  let uu____1588 =
                    let uu____1589 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1589 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1588  in
                let uu____1592 =
                  let uu____1595 =
                    let uu____1596 =
                      let uu____1597 =
                        let uu____1602 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____1602  in
                      FStar_Syntax_Embeddings.embed uu____1597 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____1596  in
                  [uu____1595]  in
                uu____1587 :: uu____1592  in
              uu____1579 :: uu____1584  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____1578
             in
          uu____1573 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____1616 =
            let uu____1621 =
              let uu____1622 =
                let uu____1623 =
                  let uu____1624 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1624 rng e  in
                FStar_Syntax_Syntax.as_arg uu____1623  in
              let uu____1627 =
                let uu____1630 =
                  let uu____1631 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1631  in
                let uu____1632 =
                  let uu____1635 =
                    let uu____1636 =
                      let uu____1637 =
                        let uu____1642 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____1642  in
                      FStar_Syntax_Embeddings.embed uu____1637 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____1636  in
                  [uu____1635]  in
                uu____1630 :: uu____1632  in
              uu____1622 :: uu____1627  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____1621
             in
          uu____1616 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___79_1649 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___79_1649.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___79_1649.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____1665 = FStar_Syntax_Util.head_and_args t  in
      match uu____1665 with
      | (hd1,args) ->
          let uu____1704 =
            let uu____1717 =
              let uu____1718 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1718.FStar_Syntax_Syntax.n  in
            (uu____1717, args)  in
          (match uu____1704 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1733)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____1758 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____1758
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1767)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____1792 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____1792
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1801)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____1826 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1826
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____1835)::(r,uu____1837)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____1872 = FStar_Syntax_Embeddings.unembed' w e_term l
                  in
               FStar_Util.bind_opt uu____1872
                 (fun l1  ->
                    let uu____1878 =
                      FStar_Syntax_Embeddings.unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____1878
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1887)::(t1,uu____1889)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____1924 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____1924
                 (fun b1  ->
                    let uu____1930 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____1930
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____1939)::(t1,uu____1941)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____1976 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____1976
                 (fun b1  ->
                    let uu____1982 =
                      FStar_Syntax_Embeddings.unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____1982
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1991)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____2016 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____2016
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2025)::(t1,uu____2027)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____2062 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2062
                 (fun b1  ->
                    let uu____2068 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____2068
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2077)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____2102 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____2102
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____2111)::(t1,uu____2113)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____2148 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____2148
                 (fun u1  ->
                    let uu____2154 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____2154
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                           (FStar_Reflection_Data.Tv_Uvar (u1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____2163)::(b,uu____2165)::(t1,uu____2167)::(t2,uu____2169)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____2224 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____2224
                 (fun r1  ->
                    let uu____2230 =
                      FStar_Syntax_Embeddings.unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____2230
                      (fun b1  ->
                         let uu____2236 =
                           FStar_Syntax_Embeddings.unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____2236
                           (fun t11  ->
                              let uu____2242 =
                                FStar_Syntax_Embeddings.unembed' w e_term t2
                                 in
                              FStar_Util.bind_opt uu____2242
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____2251)::(brs,uu____2253)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____2288 = FStar_Syntax_Embeddings.unembed' w e_term t1
                  in
               FStar_Util.bind_opt uu____2288
                 (fun t2  ->
                    let uu____2294 =
                      let uu____2299 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed' w uu____2299 brs  in
                    FStar_Util.bind_opt uu____2294
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2318)::(t1,uu____2320)::(tacopt,uu____2322)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____2367 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____2367
                 (fun e1  ->
                    let uu____2373 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____2373
                      (fun t2  ->
                         let uu____2379 =
                           let uu____2384 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____2384
                             tacopt
                            in
                         FStar_Util.bind_opt uu____2379
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2403)::(c,uu____2405)::(tacopt,uu____2407)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____2452 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____2452
                 (fun e1  ->
                    let uu____2458 =
                      FStar_Syntax_Embeddings.unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____2458
                      (fun c1  ->
                         let uu____2464 =
                           let uu____2469 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____2469
                             tacopt
                            in
                         FStar_Util.bind_opt uu____2464
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_36  ->
                                   FStar_Pervasives_Native.Some _0_36)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____2503 ->
               (if w
                then
                  (let uu____2517 =
                     let uu____2522 =
                       let uu____2523 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____2523
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2522)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____2517)
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
    let uu____2548 =
      let uu____2553 =
        let uu____2554 =
          let uu____2555 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____2555  in
        let uu____2556 =
          let uu____2559 =
            let uu____2560 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____2560  in
          let uu____2561 =
            let uu____2564 =
              let uu____2565 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____2565  in
            [uu____2564]  in
          uu____2559 :: uu____2561  in
        uu____2554 :: uu____2556  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____2553
       in
    uu____2548 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2584 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2584 with
    | (hd1,args) ->
        let uu____2623 =
          let uu____2636 =
            let uu____2637 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2637.FStar_Syntax_Syntax.n  in
          (uu____2636, args)  in
        (match uu____2623 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2652)::(idx,uu____2654)::(s,uu____2656)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2701 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____2701
               (fun nm1  ->
                  let uu____2707 =
                    FStar_Syntax_Embeddings.unembed' w
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____2707
                    (fun idx1  ->
                       let uu____2713 =
                         FStar_Syntax_Embeddings.unembed' w e_term s  in
                       FStar_Util.bind_opt uu____2713
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2720 ->
             (if w
              then
                (let uu____2734 =
                   let uu____2739 =
                     let uu____2740 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____2740
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____2739)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2734)
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
        let uu____2761 =
          let uu____2766 =
            let uu____2767 =
              let uu____2768 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____2768  in
            let uu____2769 =
              let uu____2772 =
                let uu____2773 =
                  let uu____2774 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____2774 rng md  in
                FStar_Syntax_Syntax.as_arg uu____2773  in
              [uu____2772]  in
            uu____2767 :: uu____2769  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____2766
           in
        uu____2761 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____2788 =
          let uu____2793 =
            let uu____2794 =
              let uu____2795 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____2795  in
            let uu____2796 =
              let uu____2799 =
                let uu____2800 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____2800  in
              [uu____2799]  in
            uu____2794 :: uu____2796  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____2793
           in
        uu____2788 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___80_2803 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___80_2803.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___80_2803.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2820 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2820 with
    | (hd1,args) ->
        let uu____2859 =
          let uu____2872 =
            let uu____2873 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2873.FStar_Syntax_Syntax.n  in
          (uu____2872, args)  in
        (match uu____2859 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2888)::(md,uu____2890)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2925 = FStar_Syntax_Embeddings.unembed' w e_term t2
                in
             FStar_Util.bind_opt uu____2925
               (fun t3  ->
                  let uu____2931 =
                    let uu____2936 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed' w uu____2936 md  in
                  FStar_Util.bind_opt uu____2931
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2955)::(post,uu____2957)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2992 = FStar_Syntax_Embeddings.unembed' w e_term pre
                in
             FStar_Util.bind_opt uu____2992
               (fun pre1  ->
                  let uu____2998 =
                    FStar_Syntax_Embeddings.unembed' w e_term post  in
                  FStar_Util.bind_opt uu____2998
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
               FStar_Reflection_Data.C_Unknown
         | uu____3022 ->
             (if w
              then
                (let uu____3036 =
                   let uu____3041 =
                     let uu____3042 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____3042
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3041)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3036)
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
    let uu___81_3058 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___81_3058.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___81_3058.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3075 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3075 with
    | (hd1,args) ->
        let uu____3114 =
          let uu____3127 =
            let uu____3128 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3128.FStar_Syntax_Syntax.n  in
          (uu____3127, args)  in
        (match uu____3114 with
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
         | uu____3186 ->
             (if w
              then
                (let uu____3200 =
                   let uu____3205 =
                     let uu____3206 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____3206
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3205)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3200)
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
    let uu____3236 =
      let uu____3237 = FStar_Syntax_Subst.compress t  in
      uu____3237.FStar_Syntax_Syntax.n  in
    match uu____3236 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____3243 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____3243
    | uu____3244 ->
        (if w
         then
           (let uu____3246 =
              let uu____3251 =
                let uu____3252 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____3252
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3251)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3246)
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
        let uu____3271 =
          let uu____3276 =
            let uu____3277 =
              let uu____3278 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____3278  in
            let uu____3279 =
              let uu____3282 =
                let uu____3283 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____3283  in
              let uu____3284 =
                let uu____3287 =
                  let uu____3288 =
                    FStar_Syntax_Embeddings.embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3288  in
                let uu____3289 =
                  let uu____3292 =
                    let uu____3293 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3293  in
                  [uu____3292]  in
                uu____3287 :: uu____3289  in
              uu____3282 :: uu____3284  in
            uu____3277 :: uu____3279  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____3276
           in
        uu____3271 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3298 =
          let uu____3303 =
            let uu____3304 =
              let uu____3305 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3305  in
            let uu____3308 =
              let uu____3311 =
                let uu____3312 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____3312  in
              [uu____3311]  in
            uu____3304 :: uu____3308  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____3303
           in
        uu____3298 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3327 =
          let uu____3332 =
            let uu____3333 =
              let uu____3334 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3334  in
            let uu____3337 =
              let uu____3340 =
                let uu____3341 =
                  FStar_Syntax_Embeddings.embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____3341  in
              let uu____3342 =
                let uu____3345 =
                  let uu____3346 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____3346  in
                let uu____3347 =
                  let uu____3350 =
                    let uu____3351 =
                      let uu____3352 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      FStar_Syntax_Embeddings.embed uu____3352 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____3351  in
                  [uu____3350]  in
                uu____3345 :: uu____3347  in
              uu____3340 :: uu____3342  in
            uu____3333 :: uu____3337  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____3332
           in
        uu____3327 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___82_3367 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___82_3367.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___82_3367.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3384 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3384 with
    | (hd1,args) ->
        let uu____3423 =
          let uu____3436 =
            let uu____3437 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3437.FStar_Syntax_Syntax.n  in
          (uu____3436, args)  in
        (match uu____3423 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3452)::(bs,uu____3454)::(t2,uu____3456)::(dcs,uu____3458)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____3513 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____3513
               (fun nm1  ->
                  let uu____3527 =
                    FStar_Syntax_Embeddings.unembed' w e_binders bs  in
                  FStar_Util.bind_opt uu____3527
                    (fun bs1  ->
                       let uu____3533 =
                         FStar_Syntax_Embeddings.unembed' w e_term t2  in
                       FStar_Util.bind_opt uu____3533
                         (fun t3  ->
                            let uu____3539 =
                              let uu____3546 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_string_list
                                 in
                              FStar_Syntax_Embeddings.unembed' w uu____3546
                                dcs
                               in
                            FStar_Util.bind_opt uu____3539
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_42  ->
                                      FStar_Pervasives_Native.Some _0_42)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____3579)::(fvar1,uu____3581)::(ty,uu____3583)::(t2,uu____3585)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____3640 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____3640
               (fun r1  ->
                  let uu____3646 =
                    FStar_Syntax_Embeddings.unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____3646
                    (fun fvar2  ->
                       let uu____3652 =
                         FStar_Syntax_Embeddings.unembed' w e_term ty  in
                       FStar_Util.bind_opt uu____3652
                         (fun ty1  ->
                            let uu____3658 =
                              FStar_Syntax_Embeddings.unembed' w e_term t2
                               in
                            FStar_Util.bind_opt uu____3658
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____3680 ->
             (if w
              then
                (let uu____3694 =
                   let uu____3699 =
                     let uu____3700 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____3700
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3699)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3694)
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
          let uu____3717 =
            let uu____3722 =
              let uu____3723 =
                let uu____3724 =
                  let uu____3725 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____3725  in
                FStar_Syntax_Syntax.as_arg uu____3724  in
              [uu____3723]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____3722
             in
          uu____3717 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____3730 =
            let uu____3735 =
              let uu____3736 =
                let uu____3737 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____3737  in
              let uu____3738 =
                let uu____3741 =
                  let uu____3742 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____3742  in
                [uu____3741]  in
              uu____3736 :: uu____3738  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____3735
             in
          uu____3730 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___83_3745 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___83_3745.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___83_3745.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3762 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3762 with
    | (hd1,args) ->
        let uu____3801 =
          let uu____3814 =
            let uu____3815 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3815.FStar_Syntax_Syntax.n  in
          (uu____3814, args)  in
        (match uu____3801 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____3845)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____3870 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_int i
                in
             FStar_Util.bind_opt uu____3870
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____3879)::(e2,uu____3881)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____3916 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____3916
               (fun e11  ->
                  let uu____3922 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____3922
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____3929 ->
             (if w
              then
                (let uu____3943 =
                   let uu____3948 =
                     let uu____3949 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____3949
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3948)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3943)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_exp unembed_exp
    FStar_Reflection_Data.fstar_refl_exp
  
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3959 =
      let uu____3964 =
        let uu____3965 =
          let uu____3966 =
            let uu____3967 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____3967
             in
          FStar_Syntax_Syntax.as_arg uu____3966  in
        [uu____3965]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____3964
       in
    uu____3959 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3976 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____3976 with
    | (bv,aq) ->
        let uu____3983 =
          let uu____3988 =
            let uu____3989 =
              let uu____3990 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____3990  in
            let uu____3991 =
              let uu____3994 =
                let uu____3995 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____3995  in
              [uu____3994]  in
            uu____3989 :: uu____3991  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____3988
           in
        uu____3983 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4004 =
      let uu____4009 =
        let uu____4010 =
          let uu____4011 =
            let uu____4012 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____4017 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____4012
              i.FStar_Syntax_Syntax.rng uu____4017
             in
          FStar_Syntax_Syntax.as_arg uu____4011  in
        [uu____4010]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____4009
       in
    uu____4004 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4030 =
      let uu____4035 =
        let uu____4036 =
          let uu____4037 =
            let uu____4038 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____4038
             in
          FStar_Syntax_Syntax.as_arg uu____4037  in
        [uu____4036]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____4035
       in
    uu____4030 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4052 =
      let uu____4057 =
        let uu____4058 =
          let uu____4059 =
            let uu____4060 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____4060
             in
          FStar_Syntax_Syntax.as_arg uu____4059  in
        [uu____4058]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____4057
       in
    uu____4052 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  