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
        let uu____212 =
          mapM_opt
            (fun uu____229  ->
               match uu____229 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____252 = unembed_term w e  in
                      FStar_Util.bind_opt uu____252
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1))))) aq1
           in
        FStar_Util.bind_opt uu____212
          (fun s  ->
             let uu____266 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____266)
         in
      let uu____267 =
        let uu____268 = FStar_Syntax_Subst.compress t  in
        uu____268.FStar_Syntax_Syntax.n  in
      match uu____267 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____279 ->
          (if w
           then
             (let uu____281 =
                let uu____286 =
                  let uu____287 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____287  in
                (FStar_Errors.Warning_NotEmbedded, uu____286)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____281)
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
    let uu___55_317 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___55_317.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___55_317.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____336 = FStar_Syntax_Util.head_and_args t1  in
    match uu____336 with
    | (hd1,args) ->
        let uu____369 =
          let uu____382 =
            let uu____383 = FStar_Syntax_Util.un_uinst hd1  in
            uu____383.FStar_Syntax_Syntax.n  in
          (uu____382, args)  in
        (match uu____369 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____426 ->
             (if w
              then
                (let uu____440 =
                   let uu____445 =
                     let uu____446 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____446
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____445)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____440)
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
    let uu____480 =
      let uu____481 = FStar_Syntax_Subst.compress t  in
      uu____481.FStar_Syntax_Syntax.n  in
    match uu____480 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____487 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____487
    | uu____488 ->
        (if w
         then
           (let uu____490 =
              let uu____495 =
                let uu____496 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____496  in
              (FStar_Errors.Warning_NotEmbedded, uu____495)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____490)
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
    let uu____526 =
      let uu____527 = FStar_Syntax_Subst.compress t  in
      uu____527.FStar_Syntax_Syntax.n  in
    match uu____526 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____533 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____533
    | uu____534 ->
        (if w
         then
           (let uu____536 =
              let uu____541 =
                let uu____542 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____542  in
              (FStar_Errors.Warning_NotEmbedded, uu____541)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____536)
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
    let uu____572 =
      let uu____573 = FStar_Syntax_Subst.compress t  in
      uu____573.FStar_Syntax_Syntax.n  in
    match uu____572 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____579 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____579
    | uu____580 ->
        (if w
         then
           (let uu____582 =
              let uu____587 =
                let uu____588 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____588  in
              (FStar_Errors.Warning_NotEmbedded, uu____587)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____582)
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
          let uu____609 =
            let uu____614 =
              let uu____615 =
                let uu____622 =
                  let uu____623 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____623  in
                FStar_Syntax_Syntax.as_arg uu____622  in
              [uu____615]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____614
             in
          uu____609 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____639 =
            let uu____644 =
              let uu____645 =
                let uu____652 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____652  in
              [uu____645]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____644
             in
          uu____639 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___56_667 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___56_667.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___56_667.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____686 = FStar_Syntax_Util.head_and_args t1  in
    match uu____686 with
    | (hd1,args) ->
        let uu____719 =
          let uu____732 =
            let uu____733 = FStar_Syntax_Util.un_uinst hd1  in
            uu____733.FStar_Syntax_Syntax.n  in
          (uu____732, args)  in
        (match uu____719 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____793)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____818 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____818
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____827)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____852 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____852
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                    (FStar_Reflection_Data.C_String s1))
         | uu____859 ->
             (if w
              then
                (let uu____873 =
                   let uu____878 =
                     let uu____879 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____879
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____878)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____873)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____887  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____900 =
            let uu____905 =
              let uu____906 =
                let uu____913 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____913  in
              [uu____906]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____905
             in
          uu____900 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____934 =
            let uu____939 =
              let uu____940 =
                let uu____947 = FStar_Syntax_Embeddings.embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____947  in
              let uu____948 =
                let uu____957 =
                  let uu____964 =
                    let uu____965 =
                      let uu____970 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____970  in
                    FStar_Syntax_Embeddings.embed uu____965 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____964  in
                [uu____957]  in
              uu____940 :: uu____948  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____939
             in
          uu____934 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____996 =
            let uu____1001 =
              let uu____1002 =
                let uu____1009 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1009  in
              [uu____1002]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1001
             in
          uu____996 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1025 =
            let uu____1030 =
              let uu____1031 =
                let uu____1038 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1038  in
              [uu____1031]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1030
             in
          uu____1025 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1055 =
            let uu____1060 =
              let uu____1061 =
                let uu____1068 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1068  in
              let uu____1069 =
                let uu____1078 =
                  let uu____1085 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____1085  in
                [uu____1078]  in
              uu____1061 :: uu____1069  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1060
             in
          uu____1055 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1122 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1122 with
      | (hd1,args) ->
          let uu____1155 =
            let uu____1166 =
              let uu____1167 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1167.FStar_Syntax_Syntax.n  in
            (uu____1166, args)  in
          (match uu____1155 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1180)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1195 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____1195
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1204)::(ps,uu____1206)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1225 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____1225
                 (fun f1  ->
                    let uu____1231 =
                      let uu____1236 =
                        let uu____1241 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1241  in
                      FStar_Syntax_Embeddings.unembed uu____1236 ps  in
                    FStar_Util.bind_opt uu____1231
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1258)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1273 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1273
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1282)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1297 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1297
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1306)::(t2,uu____1308)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1327 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1327
                 (fun bv1  ->
                    let uu____1333 =
                      FStar_Syntax_Embeddings.unembed e_term t2  in
                    FStar_Util.bind_opt uu____1333
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1340 ->
               (if w
                then
                  (let uu____1352 =
                     let uu____1357 =
                       let uu____1358 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1358
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1357)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1352)
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
    let uu____1385 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1385
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1399 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1399 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1421 =
            let uu____1426 =
              let uu____1427 =
                let uu____1434 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1434  in
              [uu____1427]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1426
             in
          uu____1421 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1450 =
            let uu____1455 =
              let uu____1456 =
                let uu____1463 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1463  in
              [uu____1456]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1455
             in
          uu____1450 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1479 =
            let uu____1484 =
              let uu____1485 =
                let uu____1492 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1492  in
              [uu____1485]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1484
             in
          uu____1479 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1509 =
            let uu____1514 =
              let uu____1515 =
                let uu____1522 =
                  let uu____1523 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1523 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1522  in
              let uu____1526 =
                let uu____1535 =
                  let uu____1542 =
                    let uu____1543 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1543 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1542  in
                [uu____1535]  in
              uu____1515 :: uu____1526  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1514
             in
          uu____1509 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1576 =
            let uu____1581 =
              let uu____1582 =
                let uu____1589 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1589  in
              let uu____1590 =
                let uu____1599 =
                  let uu____1606 =
                    let uu____1607 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1607 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1606  in
                [uu____1599]  in
              uu____1582 :: uu____1590  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1581
             in
          uu____1576 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1632 =
            let uu____1637 =
              let uu____1638 =
                let uu____1645 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1645  in
              let uu____1646 =
                let uu____1655 =
                  let uu____1662 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1662  in
                [uu____1655]  in
              uu____1638 :: uu____1646  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1637
             in
          uu____1632 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1684 =
            let uu____1689 =
              let uu____1690 =
                let uu____1697 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1697  in
              [uu____1690]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____1689
             in
          uu____1684 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1714 =
            let uu____1719 =
              let uu____1720 =
                let uu____1727 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1727  in
              let uu____1728 =
                let uu____1737 =
                  let uu____1744 =
                    let uu____1745 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1745 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1744  in
                [uu____1737]  in
              uu____1720 :: uu____1728  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____1719
             in
          uu____1714 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1769 =
            let uu____1774 =
              let uu____1775 =
                let uu____1782 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____1782  in
              [uu____1775]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____1774
             in
          uu____1769 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,g,bs,t1) ->
          (failwith "FIXME! Embed gamma!";
           (let uu____1802 =
              let uu____1807 =
                let uu____1808 =
                  let uu____1815 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_int rng u
                     in
                  FStar_Syntax_Syntax.as_arg uu____1815  in
                let uu____1816 =
                  let uu____1825 =
                    let uu____1832 =
                      let uu____1833 =
                        FStar_Syntax_Embeddings.e_list e_binder  in
                      FStar_Syntax_Embeddings.embed uu____1833 rng []  in
                    FStar_Syntax_Syntax.as_arg uu____1832  in
                  let uu____1840 =
                    let uu____1849 =
                      let uu____1856 =
                        let uu____1857 =
                          FStar_Syntax_Embeddings.e_list e_binder  in
                        FStar_Syntax_Embeddings.embed uu____1857 rng bs  in
                      FStar_Syntax_Syntax.as_arg uu____1856  in
                    let uu____1864 =
                      let uu____1873 =
                        let uu____1880 =
                          let uu____1881 = e_term_aq aq  in
                          FStar_Syntax_Embeddings.embed uu____1881 rng t1  in
                        FStar_Syntax_Syntax.as_arg uu____1880  in
                      [uu____1873]  in
                    uu____1849 :: uu____1864  in
                  uu____1825 :: uu____1840  in
                uu____1808 :: uu____1816  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
                uu____1807
               in
            uu____1802 FStar_Pervasives_Native.None rng))
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1920 =
            let uu____1925 =
              let uu____1926 =
                let uu____1933 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1933  in
              let uu____1934 =
                let uu____1943 =
                  let uu____1950 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____1950  in
                let uu____1951 =
                  let uu____1960 =
                    let uu____1967 =
                      let uu____1968 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____1968 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____1967  in
                  let uu____1971 =
                    let uu____1980 =
                      let uu____1987 =
                        let uu____1988 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____1988 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____1987  in
                    [uu____1980]  in
                  uu____1960 :: uu____1971  in
                uu____1943 :: uu____1951  in
              uu____1926 :: uu____1934  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____1925
             in
          uu____1920 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2029 =
            let uu____2034 =
              let uu____2035 =
                let uu____2042 =
                  let uu____2043 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2043 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____2042  in
              let uu____2046 =
                let uu____2055 =
                  let uu____2062 =
                    let uu____2063 =
                      let uu____2072 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2072  in
                    FStar_Syntax_Embeddings.embed uu____2063 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2062  in
                [uu____2055]  in
              uu____2035 :: uu____2046  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2034
             in
          uu____2029 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2116 =
            let uu____2121 =
              let uu____2122 =
                let uu____2129 =
                  let uu____2130 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2130 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2129  in
              let uu____2133 =
                let uu____2142 =
                  let uu____2149 =
                    let uu____2150 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2150 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2149  in
                let uu____2153 =
                  let uu____2162 =
                    let uu____2169 =
                      let uu____2170 =
                        let uu____2175 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2175  in
                      FStar_Syntax_Embeddings.embed uu____2170 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2169  in
                  [uu____2162]  in
                uu____2142 :: uu____2153  in
              uu____2122 :: uu____2133  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2121
             in
          uu____2116 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2213 =
            let uu____2218 =
              let uu____2219 =
                let uu____2226 =
                  let uu____2227 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2227 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2226  in
              let uu____2230 =
                let uu____2239 =
                  let uu____2246 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____2246  in
                let uu____2247 =
                  let uu____2256 =
                    let uu____2263 =
                      let uu____2264 =
                        let uu____2269 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2269  in
                      FStar_Syntax_Embeddings.embed uu____2264 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2263  in
                  [uu____2256]  in
                uu____2239 :: uu____2247  in
              uu____2219 :: uu____2230  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2218
             in
          uu____2213 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___57_2300 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___57_2300.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___57_2300.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2316 = FStar_Syntax_Util.head_and_args t  in
      match uu____2316 with
      | (hd1,args) ->
          let uu____2349 =
            let uu____2360 =
              let uu____2361 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2361.FStar_Syntax_Syntax.n  in
            (uu____2360, args)  in
          (match uu____2349 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2374)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2389 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____2389
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2398)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____2413 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____2413
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____2422)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____2437 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____2437
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____2446)::(r,uu____2448)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____2467 = FStar_Syntax_Embeddings.unembed e_term l  in
               FStar_Util.bind_opt uu____2467
                 (fun l1  ->
                    let uu____2473 = FStar_Syntax_Embeddings.unembed e_argv r
                       in
                    FStar_Util.bind_opt uu____2473
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2498)::(t1,uu____2500)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____2519 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____2519
                 (fun b1  ->
                    let uu____2525 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2525
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2534)::(t1,uu____2536)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____2555 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____2555
                 (fun b1  ->
                    let uu____2561 =
                      FStar_Syntax_Embeddings.unembed e_comp t1  in
                    FStar_Util.bind_opt uu____2561
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2570)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____2585 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____2585
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2594)::(t1,uu____2596)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____2615 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____2615
                 (fun b1  ->
                    let uu____2621 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2621
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2630)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____2645 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____2645
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____2654)::(g,uu____2656)::(bs,uu____2658)::(t1,uu____2660)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____2687 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____2687
                 (fun u1  ->
                    let uu____2693 =
                      let uu____2698 =
                        FStar_Syntax_Embeddings.e_list e_binder  in
                      FStar_Syntax_Embeddings.unembed uu____2698 bs  in
                    FStar_Util.bind_opt uu____2693
                      (fun bs1  ->
                         let uu____2712 =
                           FStar_Syntax_Embeddings.unembed e_term t1  in
                         FStar_Util.bind_opt uu____2712
                           (fun t2  ->
                              failwith "FIXME! UNEMBED GAMMA!";
                              FStar_All.pipe_left
                                (fun _0_33  ->
                                   FStar_Pervasives_Native.Some _0_33)
                                (FStar_Reflection_Data.Tv_Uvar
                                   (u1, [], bs1, t2)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____2723)::(b,uu____2725)::(t1,uu____2727)::(t2,uu____2729)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____2756 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____2756
                 (fun r1  ->
                    let uu____2762 = FStar_Syntax_Embeddings.unembed e_bv b
                       in
                    FStar_Util.bind_opt uu____2762
                      (fun b1  ->
                         let uu____2768 =
                           FStar_Syntax_Embeddings.unembed e_term t1  in
                         FStar_Util.bind_opt uu____2768
                           (fun t11  ->
                              let uu____2774 =
                                FStar_Syntax_Embeddings.unembed e_term t2  in
                              FStar_Util.bind_opt uu____2774
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_34  ->
                                        FStar_Pervasives_Native.Some _0_34)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____2783)::(brs,uu____2785)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____2804 = FStar_Syntax_Embeddings.unembed e_term t1  in
               FStar_Util.bind_opt uu____2804
                 (fun t2  ->
                    let uu____2810 =
                      let uu____2819 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed uu____2819 brs  in
                    FStar_Util.bind_opt uu____2810
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2858)::(t1,uu____2860)::(tacopt,uu____2862)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____2885 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2885
                 (fun e1  ->
                    let uu____2891 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2891
                      (fun t2  ->
                         let uu____2897 =
                           let uu____2902 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2902 tacopt
                            in
                         FStar_Util.bind_opt uu____2897
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_36  ->
                                   FStar_Pervasives_Native.Some _0_36)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2921)::(c,uu____2923)::(tacopt,uu____2925)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____2948 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2948
                 (fun e1  ->
                    let uu____2954 = FStar_Syntax_Embeddings.unembed e_comp c
                       in
                    FStar_Util.bind_opt uu____2954
                      (fun c1  ->
                         let uu____2960 =
                           let uu____2965 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2965 tacopt
                            in
                         FStar_Util.bind_opt uu____2960
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
           | uu____2995 ->
               (if w
                then
                  (let uu____3007 =
                     let uu____3012 =
                       let uu____3013 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3013
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3012)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3007)
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
    let uu____3038 =
      let uu____3043 =
        let uu____3044 =
          let uu____3051 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3051  in
        let uu____3052 =
          let uu____3061 =
            let uu____3068 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3068  in
          let uu____3069 =
            let uu____3078 =
              let uu____3085 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____3085  in
            [uu____3078]  in
          uu____3061 :: uu____3069  in
        uu____3044 :: uu____3052  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3043
       in
    uu____3038 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3128 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3128 with
    | (hd1,args) ->
        let uu____3161 =
          let uu____3172 =
            let uu____3173 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3173.FStar_Syntax_Syntax.n  in
          (uu____3172, args)  in
        (match uu____3161 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3186)::(idx,uu____3188)::(s,uu____3190)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____3213 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____3213
               (fun nm1  ->
                  let uu____3219 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____3219
                    (fun idx1  ->
                       let uu____3225 =
                         FStar_Syntax_Embeddings.unembed e_term s  in
                       FStar_Util.bind_opt uu____3225
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_39  ->
                                 FStar_Pervasives_Native.Some _0_39)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____3232 ->
             (if w
              then
                (let uu____3244 =
                   let uu____3249 =
                     let uu____3250 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____3250
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3249)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3244)
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
        let uu____3271 =
          let uu____3276 =
            let uu____3277 =
              let uu____3284 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____3284  in
            let uu____3285 =
              let uu____3294 =
                let uu____3301 =
                  let uu____3302 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____3302 rng md  in
                FStar_Syntax_Syntax.as_arg uu____3301  in
              [uu____3294]  in
            uu____3277 :: uu____3285  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____3276
           in
        uu____3271 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3334 =
          let uu____3339 =
            let uu____3340 =
              let uu____3347 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____3347  in
            let uu____3348 =
              let uu____3357 =
                let uu____3364 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____3364  in
              [uu____3357]  in
            uu____3340 :: uu____3348  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____3339
           in
        uu____3334 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___58_3385 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___58_3385.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___58_3385.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3402 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3402 with
    | (hd1,args) ->
        let uu____3435 =
          let uu____3446 =
            let uu____3447 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3447.FStar_Syntax_Syntax.n  in
          (uu____3446, args)  in
        (match uu____3435 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____3460)::(md,uu____3462)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____3481 = FStar_Syntax_Embeddings.unembed e_term t2  in
             FStar_Util.bind_opt uu____3481
               (fun t3  ->
                  let uu____3487 =
                    let uu____3492 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed uu____3492 md  in
                  FStar_Util.bind_opt uu____3487
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____3511)::(post,uu____3513)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____3532 = FStar_Syntax_Embeddings.unembed e_term pre  in
             FStar_Util.bind_opt uu____3532
               (fun pre1  ->
                  let uu____3538 =
                    FStar_Syntax_Embeddings.unembed e_term post  in
                  FStar_Util.bind_opt uu____3538
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
         | uu____3558 ->
             (if w
              then
                (let uu____3570 =
                   let uu____3575 =
                     let uu____3576 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____3576
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3575)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3570)
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
    let uu___59_3596 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___59_3596.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___59_3596.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3615 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3615 with
    | (hd1,args) ->
        let uu____3648 =
          let uu____3661 =
            let uu____3662 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3662.FStar_Syntax_Syntax.n  in
          (uu____3661, args)  in
        (match uu____3648 with
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
         | uu____3720 ->
             (if w
              then
                (let uu____3734 =
                   let uu____3739 =
                     let uu____3740 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____3740
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3739)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3734)
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
    let uu____3770 =
      let uu____3771 = FStar_Syntax_Subst.compress t  in
      uu____3771.FStar_Syntax_Syntax.n  in
    match uu____3770 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____3777 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____3777
    | uu____3778 ->
        (if w
         then
           (let uu____3780 =
              let uu____3785 =
                let uu____3786 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____3786
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3785)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3780)
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
        let uu____3805 =
          let uu____3810 =
            let uu____3811 =
              let uu____3818 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____3818  in
            let uu____3819 =
              let uu____3828 =
                let uu____3835 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____3835  in
              let uu____3836 =
                let uu____3845 =
                  let uu____3852 =
                    FStar_Syntax_Embeddings.embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3852  in
                let uu____3853 =
                  let uu____3862 =
                    let uu____3869 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3869  in
                  [uu____3862]  in
                uu____3845 :: uu____3853  in
              uu____3828 :: uu____3836  in
            uu____3811 :: uu____3819  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____3810
           in
        uu____3805 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3904 =
          let uu____3909 =
            let uu____3910 =
              let uu____3917 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3917  in
            let uu____3920 =
              let uu____3929 =
                let uu____3936 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____3936  in
              [uu____3929]  in
            uu____3910 :: uu____3920  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____3909
           in
        uu____3904 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3969 =
          let uu____3974 =
            let uu____3975 =
              let uu____3982 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3982  in
            let uu____3985 =
              let uu____3994 =
                let uu____4001 =
                  FStar_Syntax_Embeddings.embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____4001  in
              let uu____4004 =
                let uu____4013 =
                  let uu____4020 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____4020  in
                let uu____4021 =
                  let uu____4030 =
                    let uu____4037 =
                      let uu____4038 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      FStar_Syntax_Embeddings.embed uu____4038 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____4037  in
                  [uu____4030]  in
                uu____4013 :: uu____4021  in
              uu____3994 :: uu____4004  in
            uu____3975 :: uu____3985  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____3974
           in
        uu____3969 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___60_4083 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___60_4083.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___60_4083.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4100 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4100 with
    | (hd1,args) ->
        let uu____4133 =
          let uu____4144 =
            let uu____4145 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4145.FStar_Syntax_Syntax.n  in
          (uu____4144, args)  in
        (match uu____4133 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4158)::(bs,uu____4160)::(t2,uu____4162)::(dcs,uu____4164)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____4191 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____4191
               (fun nm1  ->
                  let uu____4205 =
                    FStar_Syntax_Embeddings.unembed e_binders bs  in
                  FStar_Util.bind_opt uu____4205
                    (fun bs1  ->
                       let uu____4219 =
                         FStar_Syntax_Embeddings.unembed e_term t2  in
                       FStar_Util.bind_opt uu____4219
                         (fun t3  ->
                            let uu____4225 =
                              let uu____4232 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_string_list
                                 in
                              FStar_Syntax_Embeddings.unembed uu____4232 dcs
                               in
                            FStar_Util.bind_opt uu____4225
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____4263)::(fvar1,uu____4265)::(ty,uu____4267)::(t2,uu____4269)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____4296 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_bool
                 r
                in
             FStar_Util.bind_opt uu____4296
               (fun r1  ->
                  let uu____4302 = FStar_Syntax_Embeddings.unembed e_fv fvar1
                     in
                  FStar_Util.bind_opt uu____4302
                    (fun fvar2  ->
                       let uu____4308 =
                         FStar_Syntax_Embeddings.unembed e_term ty  in
                       FStar_Util.bind_opt uu____4308
                         (fun ty1  ->
                            let uu____4314 =
                              FStar_Syntax_Embeddings.unembed e_term t2  in
                            FStar_Util.bind_opt uu____4314
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
         | uu____4332 ->
             (if w
              then
                (let uu____4344 =
                   let uu____4349 =
                     let uu____4350 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____4350
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4349)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4344)
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
          let uu____4371 =
            let uu____4376 =
              let uu____4377 =
                let uu____4384 =
                  let uu____4385 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____4385  in
                FStar_Syntax_Syntax.as_arg uu____4384  in
              [uu____4377]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____4376
             in
          uu____4371 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____4402 =
            let uu____4407 =
              let uu____4408 =
                let uu____4415 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____4415  in
              let uu____4416 =
                let uu____4425 =
                  let uu____4432 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____4432  in
                [uu____4425]  in
              uu____4408 :: uu____4416  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____4407
             in
          uu____4402 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___61_4453 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___61_4453.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___61_4453.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4472 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4472 with
    | (hd1,args) ->
        let uu____4505 =
          let uu____4516 =
            let uu____4517 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4517.FStar_Syntax_Syntax.n  in
          (uu____4516, args)  in
        (match uu____4505 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____4541)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____4556 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____4556
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____4565)::(e2,uu____4567)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____4586 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____4586
               (fun e11  ->
                  let uu____4592 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____4592
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____4599 ->
             (if w
              then
                (let uu____4611 =
                   let uu____4616 =
                     let uu____4617 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____4617
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4616)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4611)
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
    let uu____4631 =
      let uu____4636 =
        let uu____4637 =
          let uu____4644 =
            let uu____4645 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____4645
             in
          FStar_Syntax_Syntax.as_arg uu____4644  in
        [uu____4637]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____4636
       in
    uu____4631 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4666 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____4666 with
    | (bv,aq) ->
        let uu____4673 =
          let uu____4678 =
            let uu____4679 =
              let uu____4686 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____4686  in
            let uu____4687 =
              let uu____4696 =
                let uu____4703 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____4703  in
              [uu____4696]  in
            uu____4679 :: uu____4687  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____4678
           in
        uu____4673 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4730 =
      let uu____4735 =
        let uu____4736 =
          let uu____4743 =
            let uu____4744 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____4749 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____4744
              i.FStar_Syntax_Syntax.rng uu____4749
             in
          FStar_Syntax_Syntax.as_arg uu____4743  in
        [uu____4736]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____4735
       in
    uu____4730 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4774 =
      let uu____4779 =
        let uu____4780 =
          let uu____4787 =
            let uu____4788 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____4788
             in
          FStar_Syntax_Syntax.as_arg uu____4787  in
        [uu____4780]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____4779
       in
    uu____4774 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4814 =
      let uu____4819 =
        let uu____4820 =
          let uu____4827 =
            let uu____4828 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____4828
             in
          FStar_Syntax_Syntax.as_arg uu____4827  in
        [uu____4820]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____4819
       in
    uu____4814 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  