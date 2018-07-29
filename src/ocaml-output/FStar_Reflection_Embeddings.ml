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
            (fun uu____225  ->
               match uu____225 with
               | (bv,e) ->
                   let uu____234 = unembed_term w e  in
                   FStar_Util.bind_opt uu____234
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____212
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
          (if w
           then
             (let uu____263 =
                let uu____268 =
                  let uu____269 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____269  in
                (FStar_Errors.Warning_NotEmbedded, uu____268)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____263)
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
      | FStar_Reflection_Data.Q_Meta t ->
          let uu____298 =
            let uu____303 =
              let uu____304 =
                let uu____313 = FStar_Syntax_Embeddings.embed e_term rng t
                   in
                FStar_Syntax_Syntax.as_arg uu____313  in
              [uu____304]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____303
             in
          uu____298 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___224_332 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___224_332.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___224_332.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____351 = FStar_Syntax_Util.head_and_args t1  in
    match uu____351 with
    | (hd1,args) ->
        let uu____396 =
          let uu____411 =
            let uu____412 = FStar_Syntax_Util.un_uinst hd1  in
            uu____412.FStar_Syntax_Syntax.n  in
          (uu____411, args)  in
        (match uu____396 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____467)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____502 = FStar_Syntax_Embeddings.unembed' w e_term t2  in
             FStar_Util.bind_opt uu____502
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____507 ->
             (if w
              then
                (let uu____523 =
                   let uu____528 =
                     let uu____529 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____529
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____528)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____523)
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
    let uu____561 =
      let uu____562 = FStar_Syntax_Subst.compress t  in
      uu____562.FStar_Syntax_Syntax.n  in
    match uu____561 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____568 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____568
    | uu____569 ->
        (if w
         then
           (let uu____571 =
              let uu____576 =
                let uu____577 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____577  in
              (FStar_Errors.Warning_NotEmbedded, uu____576)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____571)
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
    let uu____607 =
      let uu____608 = FStar_Syntax_Subst.compress t  in
      uu____608.FStar_Syntax_Syntax.n  in
    match uu____607 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____614 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____614
    | uu____615 ->
        (if w
         then
           (let uu____617 =
              let uu____622 =
                let uu____623 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____623  in
              (FStar_Errors.Warning_NotEmbedded, uu____622)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____617)
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
    let uu____653 =
      let uu____654 = FStar_Syntax_Subst.compress t  in
      uu____654.FStar_Syntax_Syntax.n  in
    match uu____653 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____660 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____660
    | uu____661 ->
        (if w
         then
           (let uu____663 =
              let uu____668 =
                let uu____669 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____669  in
              (FStar_Errors.Warning_NotEmbedded, uu____668)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____663)
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
          let uu____690 =
            let uu____695 =
              let uu____696 =
                let uu____705 =
                  let uu____706 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____706  in
                FStar_Syntax_Syntax.as_arg uu____705  in
              [uu____696]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____695
             in
          uu____690 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____726 =
            let uu____731 =
              let uu____732 =
                let uu____741 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____741  in
              [uu____732]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____731
             in
          uu____726 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___225_760 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___225_760.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___225_760.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____779 = FStar_Syntax_Util.head_and_args t1  in
    match uu____779 with
    | (hd1,args) ->
        let uu____824 =
          let uu____839 =
            let uu____840 = FStar_Syntax_Util.un_uinst hd1  in
            uu____840.FStar_Syntax_Syntax.n  in
          (uu____839, args)  in
        (match uu____824 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____914)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____949 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_int i
                in
             FStar_Util.bind_opt uu____949
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____958)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____993 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____993
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1000 ->
             (if w
              then
                (let uu____1016 =
                   let uu____1021 =
                     let uu____1022 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1022
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1021)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1016)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1030  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1043 =
            let uu____1048 =
              let uu____1049 =
                let uu____1058 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____1058  in
              [uu____1049]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1048
             in
          uu____1043 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1083 =
            let uu____1088 =
              let uu____1089 =
                let uu____1098 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1098  in
              let uu____1099 =
                let uu____1110 =
                  let uu____1119 =
                    let uu____1120 =
                      let uu____1125 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1125  in
                    FStar_Syntax_Embeddings.embed uu____1120 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1119  in
                [uu____1110]  in
              uu____1089 :: uu____1099  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1088
             in
          uu____1083 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1157 =
            let uu____1162 =
              let uu____1163 =
                let uu____1172 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1172  in
              [uu____1163]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1162
             in
          uu____1157 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1192 =
            let uu____1197 =
              let uu____1198 =
                let uu____1207 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1207  in
              [uu____1198]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1197
             in
          uu____1192 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1232 =
            let uu____1237 =
              let uu____1238 =
                let uu____1247 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1247  in
              let uu____1248 =
                let uu____1259 =
                  let uu____1268 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____1268  in
                [uu____1259]  in
              uu____1238 :: uu____1248  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1237
             in
          uu____1232 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1311 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1311 with
      | (hd1,args) ->
          let uu____1356 =
            let uu____1369 =
              let uu____1370 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1370.FStar_Syntax_Syntax.n  in
            (uu____1369, args)  in
          (match uu____1356 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1385)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1410 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____1410
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1419)::(ps,uu____1421)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1456 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1456
                 (fun f1  ->
                    let uu____1462 =
                      let uu____1467 =
                        let uu____1472 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1472  in
                      FStar_Syntax_Embeddings.unembed' w uu____1467 ps  in
                    FStar_Util.bind_opt uu____1462
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1489)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1524 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1524
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1533)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1568 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1568
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1577)::(t2,uu____1579)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1630 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1630
                 (fun bv1  ->
                    let uu____1636 =
                      FStar_Syntax_Embeddings.unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1636
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1643 ->
               (if w
                then
                  (let uu____1657 =
                     let uu____1662 =
                       let uu____1663 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1663
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1662)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1657)
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
    let uu____1682 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1682
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1696 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1696 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1718 =
            let uu____1723 =
              let uu____1724 =
                let uu____1733 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1733  in
              [uu____1724]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1723
             in
          uu____1718 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1753 =
            let uu____1758 =
              let uu____1759 =
                let uu____1768 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1768  in
              [uu____1759]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1758
             in
          uu____1753 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1788 =
            let uu____1793 =
              let uu____1794 =
                let uu____1803 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1803  in
              [uu____1794]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1793
             in
          uu____1788 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1840 =
            let uu____1845 =
              let uu____1846 =
                let uu____1855 =
                  let uu____1856 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1856 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1855  in
              let uu____1859 =
                let uu____1870 =
                  let uu____1879 =
                    let uu____1880 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1880 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1879  in
                [uu____1870]  in
              uu____1846 :: uu____1859  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1845
             in
          uu____1840 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1935 =
            let uu____1940 =
              let uu____1941 =
                let uu____1950 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1950  in
              let uu____1951 =
                let uu____1962 =
                  let uu____1971 =
                    let uu____1972 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1972 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1971  in
                [uu____1962]  in
              uu____1941 :: uu____1951  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1940
             in
          uu____1935 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2019 =
            let uu____2024 =
              let uu____2025 =
                let uu____2034 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____2034  in
              let uu____2035 =
                let uu____2046 =
                  let uu____2055 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____2055  in
                [uu____2046]  in
              uu____2025 :: uu____2035  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2024
             in
          uu____2019 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2083 =
            let uu____2088 =
              let uu____2089 =
                let uu____2098 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2098  in
              [uu____2089]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2088
             in
          uu____2083 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2123 =
            let uu____2128 =
              let uu____2129 =
                let uu____2138 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____2138  in
              let uu____2139 =
                let uu____2150 =
                  let uu____2159 =
                    let uu____2160 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2160 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2159  in
                [uu____2150]  in
              uu____2129 :: uu____2139  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2128
             in
          uu____2123 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2190 =
            let uu____2195 =
              let uu____2196 =
                let uu____2205 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____2205  in
              [uu____2196]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2195
             in
          uu____2190 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2250 =
            let uu____2255 =
              let uu____2256 =
                let uu____2265 =
                  FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int
                    rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2265  in
              let uu____2266 =
                let uu____2277 =
                  let uu____2286 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2286  in
                [uu____2277]  in
              uu____2256 :: uu____2266  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2255
             in
          uu____2250 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2353 =
            let uu____2358 =
              let uu____2359 =
                let uu____2368 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2368  in
              let uu____2369 =
                let uu____2380 =
                  let uu____2389 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____2389  in
                let uu____2390 =
                  let uu____2401 =
                    let uu____2410 =
                      let uu____2411 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____2411 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2410  in
                  let uu____2414 =
                    let uu____2425 =
                      let uu____2434 =
                        let uu____2435 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____2435 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2434  in
                    [uu____2425]  in
                  uu____2401 :: uu____2414  in
                uu____2380 :: uu____2390  in
              uu____2359 :: uu____2369  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2358
             in
          uu____2353 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2502 =
            let uu____2507 =
              let uu____2508 =
                let uu____2517 =
                  let uu____2518 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2518 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____2517  in
              let uu____2521 =
                let uu____2532 =
                  let uu____2541 =
                    let uu____2542 =
                      let uu____2551 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2551  in
                    FStar_Syntax_Embeddings.embed uu____2542 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2541  in
                [uu____2532]  in
              uu____2508 :: uu____2521  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2507
             in
          uu____2502 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2613 =
            let uu____2618 =
              let uu____2619 =
                let uu____2628 =
                  let uu____2629 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2629 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2628  in
              let uu____2632 =
                let uu____2643 =
                  let uu____2652 =
                    let uu____2653 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2653 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2652  in
                let uu____2656 =
                  let uu____2667 =
                    let uu____2676 =
                      let uu____2677 =
                        let uu____2682 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2682  in
                      FStar_Syntax_Embeddings.embed uu____2677 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2676  in
                  [uu____2667]  in
                uu____2643 :: uu____2656  in
              uu____2619 :: uu____2632  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2618
             in
          uu____2613 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2740 =
            let uu____2745 =
              let uu____2746 =
                let uu____2755 =
                  let uu____2756 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2756 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2755  in
              let uu____2759 =
                let uu____2770 =
                  let uu____2779 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____2779  in
                let uu____2780 =
                  let uu____2791 =
                    let uu____2800 =
                      let uu____2801 =
                        let uu____2806 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2806  in
                      FStar_Syntax_Embeddings.embed uu____2801 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2800  in
                  [uu____2791]  in
                uu____2770 :: uu____2780  in
              uu____2746 :: uu____2759  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2745
             in
          uu____2740 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___226_2845 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___226_2845.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___226_2845.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2861 = FStar_Syntax_Util.head_and_args t  in
      match uu____2861 with
      | (hd1,args) ->
          let uu____2906 =
            let uu____2919 =
              let uu____2920 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2920.FStar_Syntax_Syntax.n  in
            (uu____2919, args)  in
          (match uu____2906 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2935)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2960 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2960
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2969)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____2994 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2994
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3003)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3028 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3028
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3037)::(r,uu____3039)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3074 = FStar_Syntax_Embeddings.unembed' w e_term l
                  in
               FStar_Util.bind_opt uu____3074
                 (fun l1  ->
                    let uu____3080 =
                      FStar_Syntax_Embeddings.unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3080
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3089)::(t1,uu____3091)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3142 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____3142
                 (fun b1  ->
                    let uu____3148 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3148
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3157)::(t1,uu____3159)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3210 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____3210
                 (fun b1  ->
                    let uu____3216 =
                      FStar_Syntax_Embeddings.unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3216
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3225)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3260 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3260
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3269)::(t1,uu____3271)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3322 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3322
                 (fun b1  ->
                    let uu____3328 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3328
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3337)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3372 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____3372
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3381)::(l,uu____3383)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3434 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3434
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3445)::(b,uu____3447)::(t1,uu____3449)::(t2,uu____3451)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3534 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3534
                 (fun r1  ->
                    let uu____3540 =
                      FStar_Syntax_Embeddings.unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3540
                      (fun b1  ->
                         let uu____3546 =
                           FStar_Syntax_Embeddings.unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3546
                           (fun t11  ->
                              let uu____3552 =
                                FStar_Syntax_Embeddings.unembed' w e_term t2
                                 in
                              FStar_Util.bind_opt uu____3552
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3561)::(brs,uu____3563)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3614 = FStar_Syntax_Embeddings.unembed' w e_term t1
                  in
               FStar_Util.bind_opt uu____3614
                 (fun t2  ->
                    let uu____3620 =
                      let uu____3625 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed' w uu____3625 brs  in
                    FStar_Util.bind_opt uu____3620
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3644)::(t1,uu____3646)::(tacopt,uu____3648)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3715 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____3715
                 (fun e1  ->
                    let uu____3721 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3721
                      (fun t2  ->
                         let uu____3727 =
                           let uu____3732 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____3732
                             tacopt
                            in
                         FStar_Util.bind_opt uu____3727
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3751)::(c,uu____3753)::(tacopt,uu____3755)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3822 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____3822
                 (fun e1  ->
                    let uu____3828 =
                      FStar_Syntax_Embeddings.unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3828
                      (fun c1  ->
                         let uu____3834 =
                           let uu____3839 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____3839
                             tacopt
                            in
                         FStar_Util.bind_opt uu____3834
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
           | uu____3877 ->
               (if w
                then
                  (let uu____3891 =
                     let uu____3896 =
                       let uu____3897 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3897
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3896)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3891)
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
    let uu____3920 =
      let uu____3925 =
        let uu____3926 =
          let uu____3935 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3935  in
        let uu____3936 =
          let uu____3947 =
            let uu____3956 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3956  in
          let uu____3957 =
            let uu____3968 =
              let uu____3977 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____3977  in
            [uu____3968]  in
          uu____3947 :: uu____3957  in
        uu____3926 :: uu____3936  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3925
       in
    uu____3920 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4028 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4028 with
    | (hd1,args) ->
        let uu____4073 =
          let uu____4086 =
            let uu____4087 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4087.FStar_Syntax_Syntax.n  in
          (uu____4086, args)  in
        (match uu____4073 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4102)::(idx,uu____4104)::(s,uu____4106)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4151 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4151
               (fun nm1  ->
                  let uu____4157 =
                    FStar_Syntax_Embeddings.unembed' w
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____4157
                    (fun idx1  ->
                       let uu____4163 =
                         FStar_Syntax_Embeddings.unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4163
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4170 ->
             (if w
              then
                (let uu____4184 =
                   let uu____4189 =
                     let uu____4190 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4190
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4189)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4184)
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
        let uu____4219 =
          let uu____4224 =
            let uu____4225 =
              let uu____4234 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4234  in
            let uu____4235 =
              let uu____4246 =
                let uu____4255 =
                  let uu____4256 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____4256 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4255  in
              [uu____4246]  in
            uu____4225 :: uu____4235  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4224
           in
        uu____4219 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4302 =
          let uu____4307 =
            let uu____4308 =
              let uu____4317 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____4317  in
            let uu____4318 =
              let uu____4329 =
                let uu____4338 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4338  in
              [uu____4329]  in
            uu____4308 :: uu____4318  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4307
           in
        uu____4302 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___227_4365 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___227_4365.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___227_4365.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4382 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4382 with
    | (hd1,args) ->
        let uu____4427 =
          let uu____4440 =
            let uu____4441 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4441.FStar_Syntax_Syntax.n  in
          (uu____4440, args)  in
        (match uu____4427 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4456)::(md,uu____4458)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4493 = FStar_Syntax_Embeddings.unembed' w e_term t2
                in
             FStar_Util.bind_opt uu____4493
               (fun t3  ->
                  let uu____4499 =
                    let uu____4504 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed' w uu____4504 md  in
                  FStar_Util.bind_opt uu____4499
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4523)::(post,uu____4525)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4576 = FStar_Syntax_Embeddings.unembed' w e_term pre
                in
             FStar_Util.bind_opt uu____4576
               (fun pre1  ->
                  let uu____4582 =
                    FStar_Syntax_Embeddings.unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4582
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
         | uu____4610 ->
             (if w
              then
                (let uu____4624 =
                   let uu____4629 =
                     let uu____4630 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4630
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4629)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4624)
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
    let uu___228_4650 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___228_4650.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___228_4650.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4669 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4669 with
    | (hd1,args) ->
        let uu____4714 =
          let uu____4729 =
            let uu____4730 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4730.FStar_Syntax_Syntax.n  in
          (uu____4729, args)  in
        (match uu____4714 with
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
         | uu____4802 ->
             (if w
              then
                (let uu____4818 =
                   let uu____4823 =
                     let uu____4824 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4824
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4823)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4818)
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
    let uu____4854 =
      let uu____4855 = FStar_Syntax_Subst.compress t  in
      uu____4855.FStar_Syntax_Syntax.n  in
    match uu____4854 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____4861 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____4861
    | uu____4862 ->
        (if w
         then
           (let uu____4864 =
              let uu____4869 =
                let uu____4870 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4870
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4869)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4864)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt
  
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident rng i =
    let uu____4894 =
      let uu____4899 = FStar_Ident.range_of_id i  in
      let uu____4900 = FStar_Ident.text_of_id i  in (uu____4899, uu____4900)
       in
    FStar_Syntax_Embeddings.embed repr rng uu____4894  in
  let unembed_ident w t =
    let uu____4920 = FStar_Syntax_Embeddings.unembed' w repr t  in
    match uu____4920 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4939 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4939
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____4944 =
    FStar_Syntax_Syntax.t_tuple2_of FStar_Syntax_Syntax.t_range
      FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb embed_ident unembed_ident uu____4944 
let (e_univ_name :
  FStar_Syntax_Syntax.univ_name FStar_Syntax_Embeddings.embedding) = e_ident 
let (e_univ_names :
  FStar_Syntax_Syntax.univ_name Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_univ_name 
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,univs1,ty,t) ->
        let uu____4981 =
          let uu____4986 =
            let uu____4987 =
              let uu____4996 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____4996  in
            let uu____4997 =
              let uu____5008 =
                let uu____5017 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____5017  in
              let uu____5018 =
                let uu____5029 =
                  let uu____5038 =
                    FStar_Syntax_Embeddings.embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5038  in
                let uu____5041 =
                  let uu____5052 =
                    let uu____5061 =
                      FStar_Syntax_Embeddings.embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5061  in
                  let uu____5062 =
                    let uu____5073 =
                      let uu____5082 =
                        FStar_Syntax_Embeddings.embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5082  in
                    [uu____5073]  in
                  uu____5052 :: uu____5062  in
                uu____5029 :: uu____5041  in
              uu____5008 :: uu____5018  in
            uu____4987 :: uu____4997  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4986
           in
        uu____4981 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5143 =
          let uu____5148 =
            let uu____5149 =
              let uu____5158 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____5158  in
            let uu____5161 =
              let uu____5172 =
                let uu____5181 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____5181  in
              [uu____5172]  in
            uu____5149 :: uu____5161  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5148
           in
        uu____5143 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5249 =
          let uu____5254 =
            let uu____5255 =
              let uu____5264 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____5264  in
            let uu____5267 =
              let uu____5278 =
                let uu____5287 =
                  FStar_Syntax_Embeddings.embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5287  in
              let uu____5290 =
                let uu____5301 =
                  let uu____5310 =
                    FStar_Syntax_Embeddings.embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5310  in
                let uu____5311 =
                  let uu____5322 =
                    let uu____5331 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5331  in
                  let uu____5332 =
                    let uu____5343 =
                      let uu____5352 =
                        let uu____5353 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        FStar_Syntax_Embeddings.embed uu____5353 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5352  in
                    [uu____5343]  in
                  uu____5322 :: uu____5332  in
                uu____5301 :: uu____5311  in
              uu____5278 :: uu____5290  in
            uu____5255 :: uu____5267  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5254
           in
        uu____5249 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___229_5416 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___229_5416.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___229_5416.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5433 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5433 with
    | (hd1,args) ->
        let uu____5478 =
          let uu____5491 =
            let uu____5492 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5492.FStar_Syntax_Syntax.n  in
          (uu____5491, args)  in
        (match uu____5478 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5507)::(us,uu____5509)::(bs,uu____5511)::(t2,uu____5513)::
            (dcs,uu____5515)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5580 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____5580
               (fun nm1  ->
                  let uu____5594 =
                    FStar_Syntax_Embeddings.unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5594
                    (fun us1  ->
                       let uu____5608 =
                         FStar_Syntax_Embeddings.unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5608
                         (fun bs1  ->
                            let uu____5614 =
                              FStar_Syntax_Embeddings.unembed' w e_term t2
                               in
                            FStar_Util.bind_opt uu____5614
                              (fun t3  ->
                                 let uu____5620 =
                                   let uu____5627 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   FStar_Syntax_Embeddings.unembed' w
                                     uu____5627 dcs
                                    in
                                 FStar_Util.bind_opt uu____5620
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_42  ->
                                           FStar_Pervasives_Native.Some _0_42)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5660)::(fvar1,uu____5662)::(univs1,uu____5664)::
            (ty,uu____5666)::(t2,uu____5668)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5767 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____5767
               (fun r1  ->
                  let uu____5773 =
                    FStar_Syntax_Embeddings.unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5773
                    (fun fvar2  ->
                       let uu____5779 =
                         FStar_Syntax_Embeddings.unembed' w e_univ_names
                           univs1
                          in
                       FStar_Util.bind_opt uu____5779
                         (fun univs2  ->
                            let uu____5793 =
                              FStar_Syntax_Embeddings.unembed' w e_term ty
                               in
                            FStar_Util.bind_opt uu____5793
                              (fun ty1  ->
                                 let uu____5799 =
                                   FStar_Syntax_Embeddings.unembed' w e_term
                                     t2
                                    in
                                 FStar_Util.bind_opt uu____5799
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _0_43  ->
                                           FStar_Pervasives_Native.Some _0_43)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____5827 ->
             (if w
              then
                (let uu____5841 =
                   let uu____5846 =
                     let uu____5847 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5847
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5846)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5841)
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
          let uu____5868 =
            let uu____5873 =
              let uu____5874 =
                let uu____5883 =
                  let uu____5884 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5884  in
                FStar_Syntax_Syntax.as_arg uu____5883  in
              [uu____5874]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5873
             in
          uu____5868 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5905 =
            let uu____5910 =
              let uu____5911 =
                let uu____5920 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5920  in
              let uu____5921 =
                let uu____5932 =
                  let uu____5941 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5941  in
                [uu____5932]  in
              uu____5911 :: uu____5921  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5910
             in
          uu____5905 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___230_5968 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___230_5968.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___230_5968.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5987 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5987 with
    | (hd1,args) ->
        let uu____6032 =
          let uu____6045 =
            let uu____6046 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6046.FStar_Syntax_Syntax.n  in
          (uu____6045, args)  in
        (match uu____6032 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6076)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6101 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_int i
                in
             FStar_Util.bind_opt uu____6101
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6110)::(e2,uu____6112)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6147 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6147
               (fun e11  ->
                  let uu____6153 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6153
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6160 ->
             (if w
              then
                (let uu____6174 =
                   let uu____6179 =
                     let uu____6180 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6180
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6179)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6174)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_exp unembed_exp
    FStar_Reflection_Data.fstar_refl_exp
  
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv 
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_Syntax_Embeddings.embedding) = e_term 
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_attribute 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6196 =
      let uu____6201 =
        let uu____6202 =
          let uu____6211 =
            let uu____6212 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____6212
             in
          FStar_Syntax_Syntax.as_arg uu____6211  in
        [uu____6202]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____6201
       in
    uu____6196 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6237 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____6237 with
    | (bv,aq) ->
        let uu____6244 =
          let uu____6249 =
            let uu____6250 =
              let uu____6259 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____6259  in
            let uu____6260 =
              let uu____6271 =
                let uu____6280 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____6280  in
              [uu____6271]  in
            uu____6250 :: uu____6260  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____6249
           in
        uu____6244 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6313 =
      let uu____6318 =
        let uu____6319 =
          let uu____6328 =
            let uu____6329 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____6334 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____6329
              i.FStar_Syntax_Syntax.rng uu____6334
             in
          FStar_Syntax_Syntax.as_arg uu____6328  in
        [uu____6319]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____6318
       in
    uu____6313 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6363 =
      let uu____6368 =
        let uu____6369 =
          let uu____6378 =
            let uu____6379 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____6379
             in
          FStar_Syntax_Syntax.as_arg uu____6378  in
        [uu____6369]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____6368
       in
    uu____6363 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6409 =
      let uu____6414 =
        let uu____6415 =
          let uu____6424 =
            let uu____6425 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____6425
             in
          FStar_Syntax_Syntax.as_arg uu____6424  in
        [uu____6415]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6414
       in
    uu____6409 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  