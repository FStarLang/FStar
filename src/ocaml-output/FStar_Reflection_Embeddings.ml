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
          let uu____1228 =
            let uu____1233 =
              let uu____1234 =
                let uu____1243 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1243  in
              let uu____1244 =
                let uu____1255 =
                  let uu____1264 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____1264  in
                [uu____1255]  in
              uu____1234 :: uu____1244  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1233
             in
          uu____1228 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1307 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1307 with
      | (hd1,args) ->
          let uu____1352 =
            let uu____1365 =
              let uu____1366 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1366.FStar_Syntax_Syntax.n  in
            (uu____1365, args)  in
          (match uu____1352 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1381)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1406 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____1406
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1415)::(ps,uu____1417)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1452 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1452
                 (fun f1  ->
                    let uu____1458 =
                      let uu____1463 =
                        let uu____1468 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1468  in
                      FStar_Syntax_Embeddings.unembed' w uu____1463 ps  in
                    FStar_Util.bind_opt uu____1458
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1485)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1510 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1510
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1519)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1544 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1544
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1553)::(t2,uu____1555)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1590 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1590
                 (fun bv1  ->
                    let uu____1596 =
                      FStar_Syntax_Embeddings.unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1596
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1603 ->
               (if w
                then
                  (let uu____1617 =
                     let uu____1622 =
                       let uu____1623 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1623
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1622)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1617)
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
    let uu____1642 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1642
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1656 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1656 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1678 =
            let uu____1683 =
              let uu____1684 =
                let uu____1693 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1693  in
              [uu____1684]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1683
             in
          uu____1678 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1713 =
            let uu____1718 =
              let uu____1719 =
                let uu____1728 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1728  in
              [uu____1719]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1718
             in
          uu____1713 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1748 =
            let uu____1753 =
              let uu____1754 =
                let uu____1763 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1763  in
              [uu____1754]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1753
             in
          uu____1748 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1784 =
            let uu____1789 =
              let uu____1790 =
                let uu____1799 =
                  let uu____1800 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1800 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1799  in
              let uu____1803 =
                let uu____1814 =
                  let uu____1823 =
                    let uu____1824 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1824 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1823  in
                [uu____1814]  in
              uu____1790 :: uu____1803  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1789
             in
          uu____1784 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1863 =
            let uu____1868 =
              let uu____1869 =
                let uu____1878 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1878  in
              let uu____1879 =
                let uu____1890 =
                  let uu____1899 =
                    let uu____1900 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1900 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1899  in
                [uu____1890]  in
              uu____1869 :: uu____1879  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1868
             in
          uu____1863 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1931 =
            let uu____1936 =
              let uu____1937 =
                let uu____1946 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1946  in
              let uu____1947 =
                let uu____1958 =
                  let uu____1967 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1967  in
                [uu____1958]  in
              uu____1937 :: uu____1947  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1936
             in
          uu____1931 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1995 =
            let uu____2000 =
              let uu____2001 =
                let uu____2010 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2010  in
              [uu____2001]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2000
             in
          uu____1995 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2031 =
            let uu____2036 =
              let uu____2037 =
                let uu____2046 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____2046  in
              let uu____2047 =
                let uu____2058 =
                  let uu____2067 =
                    let uu____2068 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2068 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2067  in
                [uu____2058]  in
              uu____2037 :: uu____2047  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2036
             in
          uu____2031 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2098 =
            let uu____2103 =
              let uu____2104 =
                let uu____2113 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____2113  in
              [uu____2104]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2103
             in
          uu____2098 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2134 =
            let uu____2139 =
              let uu____2140 =
                let uu____2149 =
                  FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int
                    rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2149  in
              let uu____2150 =
                let uu____2161 =
                  let uu____2170 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2170  in
                [uu____2161]  in
              uu____2140 :: uu____2150  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2139
             in
          uu____2134 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2205 =
            let uu____2210 =
              let uu____2211 =
                let uu____2220 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2220  in
              let uu____2221 =
                let uu____2232 =
                  let uu____2241 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____2241  in
                let uu____2242 =
                  let uu____2253 =
                    let uu____2262 =
                      let uu____2263 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____2263 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2262  in
                  let uu____2266 =
                    let uu____2277 =
                      let uu____2286 =
                        let uu____2287 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____2287 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2286  in
                    [uu____2277]  in
                  uu____2253 :: uu____2266  in
                uu____2232 :: uu____2242  in
              uu____2211 :: uu____2221  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2210
             in
          uu____2205 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2338 =
            let uu____2343 =
              let uu____2344 =
                let uu____2353 =
                  let uu____2354 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2354 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____2353  in
              let uu____2357 =
                let uu____2368 =
                  let uu____2377 =
                    let uu____2378 =
                      let uu____2387 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2387  in
                    FStar_Syntax_Embeddings.embed uu____2378 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2377  in
                [uu____2368]  in
              uu____2344 :: uu____2357  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2343
             in
          uu____2338 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2437 =
            let uu____2442 =
              let uu____2443 =
                let uu____2452 =
                  let uu____2453 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2453 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2452  in
              let uu____2456 =
                let uu____2467 =
                  let uu____2476 =
                    let uu____2477 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2477 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2476  in
                let uu____2480 =
                  let uu____2491 =
                    let uu____2500 =
                      let uu____2501 =
                        let uu____2506 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2506  in
                      FStar_Syntax_Embeddings.embed uu____2501 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2500  in
                  [uu____2491]  in
                uu____2467 :: uu____2480  in
              uu____2443 :: uu____2456  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2442
             in
          uu____2437 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2552 =
            let uu____2557 =
              let uu____2558 =
                let uu____2567 =
                  let uu____2568 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2568 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2567  in
              let uu____2571 =
                let uu____2582 =
                  let uu____2591 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____2591  in
                let uu____2592 =
                  let uu____2603 =
                    let uu____2612 =
                      let uu____2613 =
                        let uu____2618 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2618  in
                      FStar_Syntax_Embeddings.embed uu____2613 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2612  in
                  [uu____2603]  in
                uu____2582 :: uu____2592  in
              uu____2558 :: uu____2571  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2557
             in
          uu____2552 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___226_2657 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___226_2657.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___226_2657.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2673 = FStar_Syntax_Util.head_and_args t  in
      match uu____2673 with
      | (hd1,args) ->
          let uu____2718 =
            let uu____2731 =
              let uu____2732 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2732.FStar_Syntax_Syntax.n  in
            (uu____2731, args)  in
          (match uu____2718 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2747)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2772 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2772
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2781)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____2806 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2806
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____2815)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____2840 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____2840
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____2849)::(r,uu____2851)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____2886 = FStar_Syntax_Embeddings.unembed' w e_term l
                  in
               FStar_Util.bind_opt uu____2886
                 (fun l1  ->
                    let uu____2892 =
                      FStar_Syntax_Embeddings.unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____2892
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2901)::(t1,uu____2903)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____2938 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____2938
                 (fun b1  ->
                    let uu____2944 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____2944
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2953)::(t1,uu____2955)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____2990 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____2990
                 (fun b1  ->
                    let uu____2996 =
                      FStar_Syntax_Embeddings.unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____2996
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3005)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3030 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3030
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3039)::(t1,uu____3041)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3076 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3076
                 (fun b1  ->
                    let uu____3082 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3082
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3091)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3116 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____3116
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3125)::(l,uu____3127)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3162 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3162
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3173)::(b,uu____3175)::(t1,uu____3177)::(t2,uu____3179)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3234 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3234
                 (fun r1  ->
                    let uu____3240 =
                      FStar_Syntax_Embeddings.unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3240
                      (fun b1  ->
                         let uu____3246 =
                           FStar_Syntax_Embeddings.unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3246
                           (fun t11  ->
                              let uu____3252 =
                                FStar_Syntax_Embeddings.unembed' w e_term t2
                                 in
                              FStar_Util.bind_opt uu____3252
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3261)::(brs,uu____3263)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3298 = FStar_Syntax_Embeddings.unembed' w e_term t1
                  in
               FStar_Util.bind_opt uu____3298
                 (fun t2  ->
                    let uu____3304 =
                      let uu____3309 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed' w uu____3309 brs  in
                    FStar_Util.bind_opt uu____3304
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3328)::(t1,uu____3330)::(tacopt,uu____3332)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3377 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____3377
                 (fun e1  ->
                    let uu____3383 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3383
                      (fun t2  ->
                         let uu____3389 =
                           let uu____3394 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____3394
                             tacopt
                            in
                         FStar_Util.bind_opt uu____3389
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3413)::(c,uu____3415)::(tacopt,uu____3417)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3462 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____3462
                 (fun e1  ->
                    let uu____3468 =
                      FStar_Syntax_Embeddings.unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3468
                      (fun c1  ->
                         let uu____3474 =
                           let uu____3479 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____3479
                             tacopt
                            in
                         FStar_Util.bind_opt uu____3474
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
           | uu____3513 ->
               (if w
                then
                  (let uu____3527 =
                     let uu____3532 =
                       let uu____3533 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3533
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3532)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3527)
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
    let uu____3556 =
      let uu____3561 =
        let uu____3562 =
          let uu____3571 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3571  in
        let uu____3572 =
          let uu____3583 =
            let uu____3592 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3592  in
          let uu____3593 =
            let uu____3604 =
              let uu____3613 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____3613  in
            [uu____3604]  in
          uu____3583 :: uu____3593  in
        uu____3562 :: uu____3572  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3561
       in
    uu____3556 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3664 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3664 with
    | (hd1,args) ->
        let uu____3709 =
          let uu____3722 =
            let uu____3723 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3723.FStar_Syntax_Syntax.n  in
          (uu____3722, args)  in
        (match uu____3709 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3738)::(idx,uu____3740)::(s,uu____3742)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____3787 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____3787
               (fun nm1  ->
                  let uu____3793 =
                    FStar_Syntax_Embeddings.unembed' w
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____3793
                    (fun idx1  ->
                       let uu____3799 =
                         FStar_Syntax_Embeddings.unembed' w e_term s  in
                       FStar_Util.bind_opt uu____3799
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____3806 ->
             (if w
              then
                (let uu____3820 =
                   let uu____3825 =
                     let uu____3826 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____3826
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3825)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3820)
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
        let uu____3847 =
          let uu____3852 =
            let uu____3853 =
              let uu____3862 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____3862  in
            let uu____3863 =
              let uu____3874 =
                let uu____3883 =
                  let uu____3884 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____3884 rng md  in
                FStar_Syntax_Syntax.as_arg uu____3883  in
              [uu____3874]  in
            uu____3853 :: uu____3863  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____3852
           in
        uu____3847 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3922 =
          let uu____3927 =
            let uu____3928 =
              let uu____3937 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____3937  in
            let uu____3938 =
              let uu____3949 =
                let uu____3958 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____3958  in
              [uu____3949]  in
            uu____3928 :: uu____3938  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____3927
           in
        uu____3922 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___227_3985 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___227_3985.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___227_3985.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4002 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4002 with
    | (hd1,args) ->
        let uu____4047 =
          let uu____4060 =
            let uu____4061 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4061.FStar_Syntax_Syntax.n  in
          (uu____4060, args)  in
        (match uu____4047 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4076)::(md,uu____4078)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4113 = FStar_Syntax_Embeddings.unembed' w e_term t2
                in
             FStar_Util.bind_opt uu____4113
               (fun t3  ->
                  let uu____4119 =
                    let uu____4124 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed' w uu____4124 md  in
                  FStar_Util.bind_opt uu____4119
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4143)::(post,uu____4145)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4180 = FStar_Syntax_Embeddings.unembed' w e_term pre
                in
             FStar_Util.bind_opt uu____4180
               (fun pre1  ->
                  let uu____4186 =
                    FStar_Syntax_Embeddings.unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4186
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
         | uu____4210 ->
             (if w
              then
                (let uu____4224 =
                   let uu____4229 =
                     let uu____4230 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4230
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4229)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4224)
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
    let uu___228_4250 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___228_4250.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___228_4250.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4269 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4269 with
    | (hd1,args) ->
        let uu____4314 =
          let uu____4329 =
            let uu____4330 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4330.FStar_Syntax_Syntax.n  in
          (uu____4329, args)  in
        (match uu____4314 with
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
         | uu____4402 ->
             (if w
              then
                (let uu____4418 =
                   let uu____4423 =
                     let uu____4424 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4424
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4423)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4418)
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
    let uu____4454 =
      let uu____4455 = FStar_Syntax_Subst.compress t  in
      uu____4455.FStar_Syntax_Syntax.n  in
    match uu____4454 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____4461 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____4461
    | uu____4462 ->
        (if w
         then
           (let uu____4464 =
              let uu____4469 =
                let uu____4470 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4470
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4469)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4464)
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
    let uu____4494 =
      let uu____4499 = FStar_Ident.range_of_id i  in
      let uu____4500 = FStar_Ident.text_of_id i  in (uu____4499, uu____4500)
       in
    FStar_Syntax_Embeddings.embed repr rng uu____4494  in
  let unembed_ident w t =
    let uu____4520 = FStar_Syntax_Embeddings.unembed' w repr t  in
    match uu____4520 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4539 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4539
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____4544 =
    FStar_Syntax_Syntax.t_tuple2_of FStar_Syntax_Syntax.t_range
      FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb embed_ident unembed_ident uu____4544 
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
        let uu____4573 =
          let uu____4578 =
            let uu____4579 =
              let uu____4588 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____4588  in
            let uu____4589 =
              let uu____4600 =
                let uu____4609 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____4609  in
              let uu____4610 =
                let uu____4621 =
                  let uu____4630 =
                    FStar_Syntax_Embeddings.embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____4630  in
                let uu____4633 =
                  let uu____4644 =
                    let uu____4653 =
                      FStar_Syntax_Embeddings.embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____4653  in
                  let uu____4654 =
                    let uu____4665 =
                      let uu____4674 =
                        FStar_Syntax_Embeddings.embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____4674  in
                    [uu____4665]  in
                  uu____4644 :: uu____4654  in
                uu____4621 :: uu____4633  in
              uu____4600 :: uu____4610  in
            uu____4579 :: uu____4589  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4578
           in
        uu____4573 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4727 =
          let uu____4732 =
            let uu____4733 =
              let uu____4742 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____4742  in
            let uu____4745 =
              let uu____4756 =
                let uu____4765 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____4765  in
              [uu____4756]  in
            uu____4733 :: uu____4745  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____4732
           in
        uu____4727 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____4809 =
          let uu____4814 =
            let uu____4815 =
              let uu____4824 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____4824  in
            let uu____4827 =
              let uu____4838 =
                let uu____4847 =
                  FStar_Syntax_Embeddings.embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____4847  in
              let uu____4850 =
                let uu____4861 =
                  let uu____4870 =
                    FStar_Syntax_Embeddings.embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____4870  in
                let uu____4871 =
                  let uu____4882 =
                    let uu____4891 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____4891  in
                  let uu____4892 =
                    let uu____4903 =
                      let uu____4912 =
                        let uu____4913 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        FStar_Syntax_Embeddings.embed uu____4913 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____4912  in
                    [uu____4903]  in
                  uu____4882 :: uu____4892  in
                uu____4861 :: uu____4871  in
              uu____4838 :: uu____4850  in
            uu____4815 :: uu____4827  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____4814
           in
        uu____4809 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___229_4976 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___229_4976.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___229_4976.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4993 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4993 with
    | (hd1,args) ->
        let uu____5038 =
          let uu____5051 =
            let uu____5052 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5052.FStar_Syntax_Syntax.n  in
          (uu____5051, args)  in
        (match uu____5038 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5067)::(us,uu____5069)::(bs,uu____5071)::(t2,uu____5073)::
            (dcs,uu____5075)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5140 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____5140
               (fun nm1  ->
                  let uu____5154 =
                    FStar_Syntax_Embeddings.unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5154
                    (fun us1  ->
                       let uu____5168 =
                         FStar_Syntax_Embeddings.unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5168
                         (fun bs1  ->
                            let uu____5174 =
                              FStar_Syntax_Embeddings.unembed' w e_term t2
                               in
                            FStar_Util.bind_opt uu____5174
                              (fun t3  ->
                                 let uu____5180 =
                                   let uu____5187 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   FStar_Syntax_Embeddings.unembed' w
                                     uu____5187 dcs
                                    in
                                 FStar_Util.bind_opt uu____5180
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_42  ->
                                           FStar_Pervasives_Native.Some _0_42)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5220)::(fvar1,uu____5222)::(univs1,uu____5224)::
            (ty,uu____5226)::(t2,uu____5228)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5293 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____5293
               (fun r1  ->
                  let uu____5299 =
                    FStar_Syntax_Embeddings.unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5299
                    (fun fvar2  ->
                       let uu____5305 =
                         FStar_Syntax_Embeddings.unembed' w e_univ_names
                           univs1
                          in
                       FStar_Util.bind_opt uu____5305
                         (fun univs2  ->
                            let uu____5319 =
                              FStar_Syntax_Embeddings.unembed' w e_term ty
                               in
                            FStar_Util.bind_opt uu____5319
                              (fun ty1  ->
                                 let uu____5325 =
                                   FStar_Syntax_Embeddings.unembed' w e_term
                                     t2
                                    in
                                 FStar_Util.bind_opt uu____5325
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
         | uu____5349 ->
             (if w
              then
                (let uu____5363 =
                   let uu____5368 =
                     let uu____5369 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5369
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5368)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5363)
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
          let uu____5390 =
            let uu____5395 =
              let uu____5396 =
                let uu____5405 =
                  let uu____5406 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5406  in
                FStar_Syntax_Syntax.as_arg uu____5405  in
              [uu____5396]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5395
             in
          uu____5390 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5427 =
            let uu____5432 =
              let uu____5433 =
                let uu____5442 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5442  in
              let uu____5443 =
                let uu____5454 =
                  let uu____5463 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5463  in
                [uu____5454]  in
              uu____5433 :: uu____5443  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5432
             in
          uu____5427 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___230_5490 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___230_5490.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___230_5490.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5509 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5509 with
    | (hd1,args) ->
        let uu____5554 =
          let uu____5567 =
            let uu____5568 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5568.FStar_Syntax_Syntax.n  in
          (uu____5567, args)  in
        (match uu____5554 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5598)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5623 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_int i
                in
             FStar_Util.bind_opt uu____5623
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____5632)::(e2,uu____5634)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____5669 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____5669
               (fun e11  ->
                  let uu____5675 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____5675
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____5682 ->
             (if w
              then
                (let uu____5696 =
                   let uu____5701 =
                     let uu____5702 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____5702
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5701)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5696)
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
    let uu____5718 =
      let uu____5723 =
        let uu____5724 =
          let uu____5733 =
            let uu____5734 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____5734
             in
          FStar_Syntax_Syntax.as_arg uu____5733  in
        [uu____5724]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____5723
       in
    uu____5718 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5759 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____5759 with
    | (bv,aq) ->
        let uu____5766 =
          let uu____5771 =
            let uu____5772 =
              let uu____5781 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____5781  in
            let uu____5782 =
              let uu____5793 =
                let uu____5802 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____5802  in
              [uu____5793]  in
            uu____5772 :: uu____5782  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____5771
           in
        uu____5766 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5835 =
      let uu____5840 =
        let uu____5841 =
          let uu____5850 =
            let uu____5851 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____5856 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____5851
              i.FStar_Syntax_Syntax.rng uu____5856
             in
          FStar_Syntax_Syntax.as_arg uu____5850  in
        [uu____5841]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____5840
       in
    uu____5835 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5885 =
      let uu____5890 =
        let uu____5891 =
          let uu____5900 =
            let uu____5901 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____5901
             in
          FStar_Syntax_Syntax.as_arg uu____5900  in
        [uu____5891]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____5890
       in
    uu____5885 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5931 =
      let uu____5936 =
        let uu____5937 =
          let uu____5946 =
            let uu____5947 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____5947
             in
          FStar_Syntax_Syntax.as_arg uu____5946  in
        [uu____5937]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____5936
       in
    uu____5931 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  