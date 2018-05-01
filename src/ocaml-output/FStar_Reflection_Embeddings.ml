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
    let uu___81_317 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___81_317.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___81_317.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____336 = FStar_Syntax_Util.head_and_args t1  in
    match uu____336 with
    | (hd1,args) ->
        let uu____375 =
          let uu____388 =
            let uu____389 = FStar_Syntax_Util.un_uinst hd1  in
            uu____389.FStar_Syntax_Syntax.n  in
          (uu____388, args)  in
        (match uu____375 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____432 ->
             (if w
              then
                (let uu____446 =
                   let uu____451 =
                     let uu____452 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____452
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____451)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____446)
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
    let uu____486 =
      let uu____487 = FStar_Syntax_Subst.compress t  in
      uu____487.FStar_Syntax_Syntax.n  in
    match uu____486 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____493 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____493
    | uu____494 ->
        (if w
         then
           (let uu____496 =
              let uu____501 =
                let uu____502 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____502  in
              (FStar_Errors.Warning_NotEmbedded, uu____501)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____496)
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
    let uu____532 =
      let uu____533 = FStar_Syntax_Subst.compress t  in
      uu____533.FStar_Syntax_Syntax.n  in
    match uu____532 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____539 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____539
    | uu____540 ->
        (if w
         then
           (let uu____542 =
              let uu____547 =
                let uu____548 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____548  in
              (FStar_Errors.Warning_NotEmbedded, uu____547)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____542)
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
    let uu____578 =
      let uu____579 = FStar_Syntax_Subst.compress t  in
      uu____579.FStar_Syntax_Syntax.n  in
    match uu____578 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____585 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____585
    | uu____586 ->
        (if w
         then
           (let uu____588 =
              let uu____593 =
                let uu____594 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____594  in
              (FStar_Errors.Warning_NotEmbedded, uu____593)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____588)
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
          let uu____615 =
            let uu____620 =
              let uu____621 =
                let uu____628 =
                  let uu____629 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____629  in
                FStar_Syntax_Syntax.as_arg uu____628  in
              [uu____621]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____620
             in
          uu____615 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____645 =
            let uu____650 =
              let uu____651 =
                let uu____658 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____658  in
              [uu____651]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____650
             in
          uu____645 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___82_673 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___82_673.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___82_673.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____692 = FStar_Syntax_Util.head_and_args t1  in
    match uu____692 with
    | (hd1,args) ->
        let uu____731 =
          let uu____744 =
            let uu____745 = FStar_Syntax_Util.un_uinst hd1  in
            uu____745.FStar_Syntax_Syntax.n  in
          (uu____744, args)  in
        (match uu____731 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____805)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____830 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____830
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____839)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____864 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____864
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                    (FStar_Reflection_Data.C_String s1))
         | uu____871 ->
             (if w
              then
                (let uu____885 =
                   let uu____890 =
                     let uu____891 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____891
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____890)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____885)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____899  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____912 =
            let uu____917 =
              let uu____918 =
                let uu____925 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____925  in
              [uu____918]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____917
             in
          uu____912 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____946 =
            let uu____951 =
              let uu____952 =
                let uu____959 = FStar_Syntax_Embeddings.embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____959  in
              let uu____960 =
                let uu____969 =
                  let uu____976 =
                    let uu____977 =
                      let uu____982 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____982  in
                    FStar_Syntax_Embeddings.embed uu____977 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____976  in
                [uu____969]  in
              uu____952 :: uu____960  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____951
             in
          uu____946 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1008 =
            let uu____1013 =
              let uu____1014 =
                let uu____1021 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1021  in
              [uu____1014]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1013
             in
          uu____1008 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1037 =
            let uu____1042 =
              let uu____1043 =
                let uu____1050 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1050  in
              [uu____1043]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1042
             in
          uu____1037 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1067 =
            let uu____1072 =
              let uu____1073 =
                let uu____1080 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1080  in
              let uu____1081 =
                let uu____1090 =
                  let uu____1097 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____1097  in
                [uu____1090]  in
              uu____1073 :: uu____1081  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1072
             in
          uu____1067 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1134 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1134 with
      | (hd1,args) ->
          let uu____1173 =
            let uu____1184 =
              let uu____1185 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1185.FStar_Syntax_Syntax.n  in
            (uu____1184, args)  in
          (match uu____1173 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1198)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1213 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____1213
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1222)::(ps,uu____1224)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1243 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____1243
                 (fun f1  ->
                    let uu____1249 =
                      let uu____1254 =
                        let uu____1259 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1259  in
                      FStar_Syntax_Embeddings.unembed uu____1254 ps  in
                    FStar_Util.bind_opt uu____1249
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1276)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1291 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1291
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1300)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1315 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1315
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1324)::(t2,uu____1326)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1345 = FStar_Syntax_Embeddings.unembed e_bv bv  in
               FStar_Util.bind_opt uu____1345
                 (fun bv1  ->
                    let uu____1351 =
                      FStar_Syntax_Embeddings.unembed e_term t2  in
                    FStar_Util.bind_opt uu____1351
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1358 ->
               (if w
                then
                  (let uu____1370 =
                     let uu____1375 =
                       let uu____1376 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1376
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1375)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1370)
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
    let uu____1403 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1403
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1417 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1417 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1439 =
            let uu____1444 =
              let uu____1445 =
                let uu____1452 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1452  in
              [uu____1445]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1444
             in
          uu____1439 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1468 =
            let uu____1473 =
              let uu____1474 =
                let uu____1481 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1481  in
              [uu____1474]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1473
             in
          uu____1468 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1497 =
            let uu____1502 =
              let uu____1503 =
                let uu____1510 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1510  in
              [uu____1503]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1502
             in
          uu____1497 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1527 =
            let uu____1532 =
              let uu____1533 =
                let uu____1540 =
                  let uu____1541 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1541 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1540  in
              let uu____1544 =
                let uu____1553 =
                  let uu____1560 =
                    let uu____1561 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1561 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1560  in
                [uu____1553]  in
              uu____1533 :: uu____1544  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1532
             in
          uu____1527 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1594 =
            let uu____1599 =
              let uu____1600 =
                let uu____1607 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1607  in
              let uu____1608 =
                let uu____1617 =
                  let uu____1624 =
                    let uu____1625 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1625 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1624  in
                [uu____1617]  in
              uu____1600 :: uu____1608  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1599
             in
          uu____1594 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1650 =
            let uu____1655 =
              let uu____1656 =
                let uu____1663 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1663  in
              let uu____1664 =
                let uu____1673 =
                  let uu____1680 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1680  in
                [uu____1673]  in
              uu____1656 :: uu____1664  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1655
             in
          uu____1650 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1702 =
            let uu____1707 =
              let uu____1708 =
                let uu____1715 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1715  in
              [uu____1708]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____1707
             in
          uu____1702 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1732 =
            let uu____1737 =
              let uu____1738 =
                let uu____1745 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1745  in
              let uu____1746 =
                let uu____1755 =
                  let uu____1762 =
                    let uu____1763 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1763 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1762  in
                [uu____1755]  in
              uu____1738 :: uu____1746  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____1737
             in
          uu____1732 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____1787 =
            let uu____1792 =
              let uu____1793 =
                let uu____1800 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____1800  in
              [uu____1793]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____1792
             in
          uu____1787 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,g,bs,t1) ->
          (failwith "FIXME! Embed gamma!";
           (let uu____1820 =
              let uu____1825 =
                let uu____1826 =
                  let uu____1833 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_int rng u
                     in
                  FStar_Syntax_Syntax.as_arg uu____1833  in
                let uu____1834 =
                  let uu____1843 =
                    let uu____1850 =
                      let uu____1851 =
                        FStar_Syntax_Embeddings.e_list e_binder  in
                      FStar_Syntax_Embeddings.embed uu____1851 rng []  in
                    FStar_Syntax_Syntax.as_arg uu____1850  in
                  let uu____1858 =
                    let uu____1867 =
                      let uu____1874 =
                        let uu____1875 =
                          FStar_Syntax_Embeddings.e_list e_binder  in
                        FStar_Syntax_Embeddings.embed uu____1875 rng bs  in
                      FStar_Syntax_Syntax.as_arg uu____1874  in
                    let uu____1882 =
                      let uu____1891 =
                        let uu____1898 =
                          let uu____1899 = e_term_aq aq  in
                          FStar_Syntax_Embeddings.embed uu____1899 rng t1  in
                        FStar_Syntax_Syntax.as_arg uu____1898  in
                      [uu____1891]  in
                    uu____1867 :: uu____1882  in
                  uu____1843 :: uu____1858  in
                uu____1826 :: uu____1834  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
                uu____1825
               in
            uu____1820 FStar_Pervasives_Native.None rng))
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____1938 =
            let uu____1943 =
              let uu____1944 =
                let uu____1951 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1951  in
              let uu____1952 =
                let uu____1961 =
                  let uu____1968 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____1968  in
                let uu____1969 =
                  let uu____1978 =
                    let uu____1985 =
                      let uu____1986 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____1986 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____1985  in
                  let uu____1989 =
                    let uu____1998 =
                      let uu____2005 =
                        let uu____2006 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____2006 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2005  in
                    [uu____1998]  in
                  uu____1978 :: uu____1989  in
                uu____1961 :: uu____1969  in
              uu____1944 :: uu____1952  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____1943
             in
          uu____1938 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2047 =
            let uu____2052 =
              let uu____2053 =
                let uu____2060 =
                  let uu____2061 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2061 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____2060  in
              let uu____2064 =
                let uu____2073 =
                  let uu____2080 =
                    let uu____2081 =
                      let uu____2090 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2090  in
                    FStar_Syntax_Embeddings.embed uu____2081 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2080  in
                [uu____2073]  in
              uu____2053 :: uu____2064  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2052
             in
          uu____2047 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2134 =
            let uu____2139 =
              let uu____2140 =
                let uu____2147 =
                  let uu____2148 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2148 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2147  in
              let uu____2151 =
                let uu____2160 =
                  let uu____2167 =
                    let uu____2168 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2168 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2167  in
                let uu____2171 =
                  let uu____2180 =
                    let uu____2187 =
                      let uu____2188 =
                        let uu____2193 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2193  in
                      FStar_Syntax_Embeddings.embed uu____2188 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2187  in
                  [uu____2180]  in
                uu____2160 :: uu____2171  in
              uu____2140 :: uu____2151  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2139
             in
          uu____2134 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2231 =
            let uu____2236 =
              let uu____2237 =
                let uu____2244 =
                  let uu____2245 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2245 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2244  in
              let uu____2248 =
                let uu____2257 =
                  let uu____2264 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____2264  in
                let uu____2265 =
                  let uu____2274 =
                    let uu____2281 =
                      let uu____2282 =
                        let uu____2287 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2287  in
                      FStar_Syntax_Embeddings.embed uu____2282 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2281  in
                  [uu____2274]  in
                uu____2257 :: uu____2265  in
              uu____2237 :: uu____2248  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2236
             in
          uu____2231 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___83_2318 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___83_2318.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___83_2318.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2334 = FStar_Syntax_Util.head_and_args t  in
      match uu____2334 with
      | (hd1,args) ->
          let uu____2373 =
            let uu____2384 =
              let uu____2385 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2385.FStar_Syntax_Syntax.n  in
            (uu____2384, args)  in
          (match uu____2373 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2398)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2413 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____2413
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2422)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____2437 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____2437
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____2446)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____2461 = FStar_Syntax_Embeddings.unembed e_fv f  in
               FStar_Util.bind_opt uu____2461
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____2470)::(r,uu____2472)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____2491 = FStar_Syntax_Embeddings.unembed e_term l  in
               FStar_Util.bind_opt uu____2491
                 (fun l1  ->
                    let uu____2497 = FStar_Syntax_Embeddings.unembed e_argv r
                       in
                    FStar_Util.bind_opt uu____2497
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2522)::(t1,uu____2524)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____2543 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____2543
                 (fun b1  ->
                    let uu____2549 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2549
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2558)::(t1,uu____2560)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____2579 = FStar_Syntax_Embeddings.unembed e_binder b
                  in
               FStar_Util.bind_opt uu____2579
                 (fun b1  ->
                    let uu____2585 =
                      FStar_Syntax_Embeddings.unembed e_comp t1  in
                    FStar_Util.bind_opt uu____2585
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2594)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____2609 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____2609
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2618)::(t1,uu____2620)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____2639 = FStar_Syntax_Embeddings.unembed e_bv b  in
               FStar_Util.bind_opt uu____2639
                 (fun b1  ->
                    let uu____2645 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2645
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2654)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____2669 = FStar_Syntax_Embeddings.unembed e_const c  in
               FStar_Util.bind_opt uu____2669
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____2678)::(g,uu____2680)::(bs,uu____2682)::(t1,uu____2684)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____2711 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____2711
                 (fun u1  ->
                    let uu____2717 =
                      let uu____2722 =
                        FStar_Syntax_Embeddings.e_list e_binder  in
                      FStar_Syntax_Embeddings.unembed uu____2722 bs  in
                    FStar_Util.bind_opt uu____2717
                      (fun bs1  ->
                         let uu____2736 =
                           FStar_Syntax_Embeddings.unembed e_term t1  in
                         FStar_Util.bind_opt uu____2736
                           (fun t2  ->
                              failwith "FIXME! UNEMBED GAMMA!";
                              FStar_All.pipe_left
                                (fun _0_33  ->
                                   FStar_Pervasives_Native.Some _0_33)
                                (FStar_Reflection_Data.Tv_Uvar
                                   (u1, [], bs1, t2)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____2747)::(b,uu____2749)::(t1,uu____2751)::(t2,uu____2753)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____2780 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____2780
                 (fun r1  ->
                    let uu____2786 = FStar_Syntax_Embeddings.unembed e_bv b
                       in
                    FStar_Util.bind_opt uu____2786
                      (fun b1  ->
                         let uu____2792 =
                           FStar_Syntax_Embeddings.unembed e_term t1  in
                         FStar_Util.bind_opt uu____2792
                           (fun t11  ->
                              let uu____2798 =
                                FStar_Syntax_Embeddings.unembed e_term t2  in
                              FStar_Util.bind_opt uu____2798
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_34  ->
                                        FStar_Pervasives_Native.Some _0_34)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____2807)::(brs,uu____2809)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____2828 = FStar_Syntax_Embeddings.unembed e_term t1  in
               FStar_Util.bind_opt uu____2828
                 (fun t2  ->
                    let uu____2834 =
                      let uu____2843 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed uu____2843 brs  in
                    FStar_Util.bind_opt uu____2834
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2882)::(t1,uu____2884)::(tacopt,uu____2886)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____2909 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2909
                 (fun e1  ->
                    let uu____2915 =
                      FStar_Syntax_Embeddings.unembed e_term t1  in
                    FStar_Util.bind_opt uu____2915
                      (fun t2  ->
                         let uu____2921 =
                           let uu____2926 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2926 tacopt
                            in
                         FStar_Util.bind_opt uu____2921
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_36  ->
                                   FStar_Pervasives_Native.Some _0_36)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____2945)::(c,uu____2947)::(tacopt,uu____2949)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____2972 = FStar_Syntax_Embeddings.unembed e_term e  in
               FStar_Util.bind_opt uu____2972
                 (fun e1  ->
                    let uu____2978 = FStar_Syntax_Embeddings.unembed e_comp c
                       in
                    FStar_Util.bind_opt uu____2978
                      (fun c1  ->
                         let uu____2984 =
                           let uu____2989 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed uu____2989 tacopt
                            in
                         FStar_Util.bind_opt uu____2984
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
           | uu____3019 ->
               (if w
                then
                  (let uu____3031 =
                     let uu____3036 =
                       let uu____3037 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3037
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3036)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3031)
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
    let uu____3062 =
      let uu____3067 =
        let uu____3068 =
          let uu____3075 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3075  in
        let uu____3076 =
          let uu____3085 =
            let uu____3092 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3092  in
          let uu____3093 =
            let uu____3102 =
              let uu____3109 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____3109  in
            [uu____3102]  in
          uu____3085 :: uu____3093  in
        uu____3068 :: uu____3076  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3067
       in
    uu____3062 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3152 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3152 with
    | (hd1,args) ->
        let uu____3191 =
          let uu____3202 =
            let uu____3203 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3203.FStar_Syntax_Syntax.n  in
          (uu____3202, args)  in
        (match uu____3191 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3216)::(idx,uu____3218)::(s,uu____3220)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____3243 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____3243
               (fun nm1  ->
                  let uu____3249 =
                    FStar_Syntax_Embeddings.unembed
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____3249
                    (fun idx1  ->
                       let uu____3255 =
                         FStar_Syntax_Embeddings.unembed e_term s  in
                       FStar_Util.bind_opt uu____3255
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_39  ->
                                 FStar_Pervasives_Native.Some _0_39)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____3262 ->
             (if w
              then
                (let uu____3274 =
                   let uu____3279 =
                     let uu____3280 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____3280
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3279)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3274)
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
        let uu____3301 =
          let uu____3306 =
            let uu____3307 =
              let uu____3314 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____3314  in
            let uu____3315 =
              let uu____3324 =
                let uu____3331 =
                  let uu____3332 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____3332 rng md  in
                FStar_Syntax_Syntax.as_arg uu____3331  in
              [uu____3324]  in
            uu____3307 :: uu____3315  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____3306
           in
        uu____3301 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3364 =
          let uu____3369 =
            let uu____3370 =
              let uu____3377 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____3377  in
            let uu____3378 =
              let uu____3387 =
                let uu____3394 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____3394  in
              [uu____3387]  in
            uu____3370 :: uu____3378  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____3369
           in
        uu____3364 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___84_3415 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___84_3415.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___84_3415.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3432 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3432 with
    | (hd1,args) ->
        let uu____3471 =
          let uu____3482 =
            let uu____3483 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3483.FStar_Syntax_Syntax.n  in
          (uu____3482, args)  in
        (match uu____3471 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____3496)::(md,uu____3498)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____3517 = FStar_Syntax_Embeddings.unembed e_term t2  in
             FStar_Util.bind_opt uu____3517
               (fun t3  ->
                  let uu____3523 =
                    let uu____3528 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed uu____3528 md  in
                  FStar_Util.bind_opt uu____3523
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____3547)::(post,uu____3549)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____3568 = FStar_Syntax_Embeddings.unembed e_term pre  in
             FStar_Util.bind_opt uu____3568
               (fun pre1  ->
                  let uu____3574 =
                    FStar_Syntax_Embeddings.unembed e_term post  in
                  FStar_Util.bind_opt uu____3574
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
         | uu____3594 ->
             (if w
              then
                (let uu____3606 =
                   let uu____3611 =
                     let uu____3612 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____3612
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3611)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3606)
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
    let uu___85_3632 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___85_3632.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___85_3632.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3651 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3651 with
    | (hd1,args) ->
        let uu____3690 =
          let uu____3703 =
            let uu____3704 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3704.FStar_Syntax_Syntax.n  in
          (uu____3703, args)  in
        (match uu____3690 with
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
         | uu____3762 ->
             (if w
              then
                (let uu____3776 =
                   let uu____3781 =
                     let uu____3782 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____3782
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3781)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3776)
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
    let uu____3812 =
      let uu____3813 = FStar_Syntax_Subst.compress t  in
      uu____3813.FStar_Syntax_Syntax.n  in
    match uu____3812 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____3819 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____3819
    | uu____3820 ->
        (if w
         then
           (let uu____3822 =
              let uu____3827 =
                let uu____3828 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____3828
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____3827)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3822)
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
        let uu____3847 =
          let uu____3852 =
            let uu____3853 =
              let uu____3860 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____3860  in
            let uu____3861 =
              let uu____3870 =
                let uu____3877 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____3877  in
              let uu____3878 =
                let uu____3887 =
                  let uu____3894 =
                    FStar_Syntax_Embeddings.embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____3894  in
                let uu____3895 =
                  let uu____3904 =
                    let uu____3911 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____3911  in
                  [uu____3904]  in
                uu____3887 :: uu____3895  in
              uu____3870 :: uu____3878  in
            uu____3853 :: uu____3861  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____3852
           in
        uu____3847 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____3946 =
          let uu____3951 =
            let uu____3952 =
              let uu____3959 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____3959  in
            let uu____3962 =
              let uu____3971 =
                let uu____3978 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____3978  in
              [uu____3971]  in
            uu____3952 :: uu____3962  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____3951
           in
        uu____3946 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____4011 =
          let uu____4016 =
            let uu____4017 =
              let uu____4024 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____4024  in
            let uu____4027 =
              let uu____4036 =
                let uu____4043 =
                  FStar_Syntax_Embeddings.embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____4043  in
              let uu____4046 =
                let uu____4055 =
                  let uu____4062 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____4062  in
                let uu____4063 =
                  let uu____4072 =
                    let uu____4079 =
                      let uu____4080 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      FStar_Syntax_Embeddings.embed uu____4080 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____4079  in
                  [uu____4072]  in
                uu____4055 :: uu____4063  in
              uu____4036 :: uu____4046  in
            uu____4017 :: uu____4027  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____4016
           in
        uu____4011 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___86_4125 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___86_4125.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___86_4125.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4142 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4142 with
    | (hd1,args) ->
        let uu____4181 =
          let uu____4192 =
            let uu____4193 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4193.FStar_Syntax_Syntax.n  in
          (uu____4192, args)  in
        (match uu____4181 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4206)::(bs,uu____4208)::(t2,uu____4210)::(dcs,uu____4212)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____4239 =
               FStar_Syntax_Embeddings.unembed
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____4239
               (fun nm1  ->
                  let uu____4253 =
                    FStar_Syntax_Embeddings.unembed e_binders bs  in
                  FStar_Util.bind_opt uu____4253
                    (fun bs1  ->
                       let uu____4267 =
                         FStar_Syntax_Embeddings.unembed e_term t2  in
                       FStar_Util.bind_opt uu____4267
                         (fun t3  ->
                            let uu____4273 =
                              let uu____4280 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_string_list
                                 in
                              FStar_Syntax_Embeddings.unembed uu____4280 dcs
                               in
                            FStar_Util.bind_opt uu____4273
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____4311)::(fvar1,uu____4313)::(ty,uu____4315)::(t2,uu____4317)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____4344 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_bool
                 r
                in
             FStar_Util.bind_opt uu____4344
               (fun r1  ->
                  let uu____4350 = FStar_Syntax_Embeddings.unembed e_fv fvar1
                     in
                  FStar_Util.bind_opt uu____4350
                    (fun fvar2  ->
                       let uu____4356 =
                         FStar_Syntax_Embeddings.unembed e_term ty  in
                       FStar_Util.bind_opt uu____4356
                         (fun ty1  ->
                            let uu____4362 =
                              FStar_Syntax_Embeddings.unembed e_term t2  in
                            FStar_Util.bind_opt uu____4362
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
         | uu____4380 ->
             (if w
              then
                (let uu____4392 =
                   let uu____4397 =
                     let uu____4398 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____4398
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4397)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4392)
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
          let uu____4419 =
            let uu____4424 =
              let uu____4425 =
                let uu____4432 =
                  let uu____4433 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____4433  in
                FStar_Syntax_Syntax.as_arg uu____4432  in
              [uu____4425]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____4424
             in
          uu____4419 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____4450 =
            let uu____4455 =
              let uu____4456 =
                let uu____4463 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____4463  in
              let uu____4464 =
                let uu____4473 =
                  let uu____4480 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____4480  in
                [uu____4473]  in
              uu____4456 :: uu____4464  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____4455
             in
          uu____4450 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___87_4501 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___87_4501.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___87_4501.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4520 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4520 with
    | (hd1,args) ->
        let uu____4559 =
          let uu____4570 =
            let uu____4571 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4571.FStar_Syntax_Syntax.n  in
          (uu____4570, args)  in
        (match uu____4559 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____4595)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____4610 =
               FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int
                 i
                in
             FStar_Util.bind_opt uu____4610
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____4619)::(e2,uu____4621)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____4640 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____4640
               (fun e11  ->
                  let uu____4646 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____4646
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____4653 ->
             (if w
              then
                (let uu____4665 =
                   let uu____4670 =
                     let uu____4671 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____4671
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4670)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4665)
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
    let uu____4685 =
      let uu____4690 =
        let uu____4691 =
          let uu____4698 =
            let uu____4699 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____4699
             in
          FStar_Syntax_Syntax.as_arg uu____4698  in
        [uu____4691]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____4690
       in
    uu____4685 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4720 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____4720 with
    | (bv,aq) ->
        let uu____4727 =
          let uu____4732 =
            let uu____4733 =
              let uu____4740 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____4740  in
            let uu____4741 =
              let uu____4750 =
                let uu____4757 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____4757  in
              [uu____4750]  in
            uu____4733 :: uu____4741  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____4732
           in
        uu____4727 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4784 =
      let uu____4789 =
        let uu____4790 =
          let uu____4797 =
            let uu____4798 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____4803 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____4798
              i.FStar_Syntax_Syntax.rng uu____4803
             in
          FStar_Syntax_Syntax.as_arg uu____4797  in
        [uu____4790]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____4789
       in
    uu____4784 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4828 =
      let uu____4833 =
        let uu____4834 =
          let uu____4841 =
            let uu____4842 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____4842
             in
          FStar_Syntax_Syntax.as_arg uu____4841  in
        [uu____4834]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____4833
       in
    uu____4828 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____4868 =
      let uu____4873 =
        let uu____4874 =
          let uu____4881 =
            let uu____4882 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____4882
             in
          FStar_Syntax_Syntax.as_arg uu____4881  in
        [uu____4874]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____4873
       in
    uu____4868 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  