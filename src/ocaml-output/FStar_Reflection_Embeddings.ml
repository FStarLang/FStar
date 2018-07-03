open Prims
let mk_emb :
  'Auu____9 .
    (FStar_Range.range -> 'Auu____9 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'Auu____9 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____9 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____51 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____51
  
let embed :
  'Auu____97 .
    'Auu____97 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____97 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____117 = FStar_Syntax_Embeddings.embed e x  in
        uu____117 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____157 .
    Prims.bool ->
      'Auu____157 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____157 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____179 = FStar_Syntax_Embeddings.unembed e x  in
        uu____179 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____218 =
      let uu____219 = FStar_Syntax_Subst.compress t  in
      uu____219.FStar_Syntax_Syntax.n  in
    match uu____218 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____225;
          FStar_Syntax_Syntax.rng = uu____226;_}
        ->
        let uu____229 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____229
    | uu____230 ->
        (if w
         then
           (let uu____232 =
              let uu____237 =
                let uu____238 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____238  in
              (FStar_Errors.Warning_NotEmbedded, uu____237)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____232)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv 
let (e_binder : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding)
  =
  let embed_binder rng b =
    FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng)
     in
  let unembed_binder w t =
    let uu____268 =
      let uu____269 = FStar_Syntax_Subst.compress t  in
      uu____269.FStar_Syntax_Syntax.n  in
    match uu____268 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____275;
          FStar_Syntax_Syntax.rng = uu____276;_}
        ->
        let uu____279 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____279
    | uu____280 ->
        (if w
         then
           (let uu____282 =
              let uu____287 =
                let uu____288 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____288  in
              (FStar_Errors.Warning_NotEmbedded, uu____287)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____282)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_binder unembed_binder FStar_Reflection_Data.fstar_refl_binder 
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
          let uu____335 = f x  in
          FStar_Util.bind_opt uu____335
            (fun x1  ->
               let uu____343 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____343
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
        let uu____409 =
          mapM_opt
            (fun uu____426  ->
               match uu____426 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____449 = unembed_term w e  in
                      FStar_Util.bind_opt uu____449
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1))))) aq1
           in
        FStar_Util.bind_opt uu____409
          (fun s  ->
             let uu____463 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____463)
         in
      let uu____464 =
        let uu____465 = FStar_Syntax_Subst.compress t  in
        uu____465.FStar_Syntax_Syntax.n  in
      match uu____464 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____476 ->
          (if w
           then
             (let uu____478 =
                let uu____483 =
                  let uu____484 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____484  in
                (FStar_Errors.Warning_NotEmbedded, uu____483)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____478)
           else ();
           FStar_Pervasives_Native.None)
       in
    mk_emb embed_term unembed_term FStar_Syntax_Syntax.t_term
  
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
          let uu____515 =
            let uu____520 =
              let uu____521 =
                let uu____530 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____530  in
              [uu____521]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____520
             in
          uu____515 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___229_549 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___229_549.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___229_549.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____568 = FStar_Syntax_Util.head_and_args t1  in
    match uu____568 with
    | (hd1,args) ->
        let uu____613 =
          let uu____628 =
            let uu____629 = FStar_Syntax_Util.un_uinst hd1  in
            uu____629.FStar_Syntax_Syntax.n  in
          (uu____628, args)  in
        (match uu____613 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____684)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____719 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____719
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____724 ->
             (if w
              then
                (let uu____740 =
                   let uu____745 =
                     let uu____746 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____746
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____745)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____740)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_aqualv unembed_aqualv FStar_Reflection_Data.fstar_refl_aqualv 
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_list e_binder 
let (e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings.embedding) =
  let embed_fv rng fv =
    FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
     in
  let unembed_fv w t =
    let uu____778 =
      let uu____779 = FStar_Syntax_Subst.compress t  in
      uu____779.FStar_Syntax_Syntax.n  in
    match uu____778 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____785;
          FStar_Syntax_Syntax.rng = uu____786;_}
        ->
        let uu____789 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____789
    | uu____790 ->
        (if w
         then
           (let uu____792 =
              let uu____797 =
                let uu____798 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____798  in
              (FStar_Errors.Warning_NotEmbedded, uu____797)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____792)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv 
let (e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding) =
  let embed_comp rng c =
    FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng)
     in
  let unembed_comp w t =
    let uu____828 =
      let uu____829 = FStar_Syntax_Subst.compress t  in
      uu____829.FStar_Syntax_Syntax.n  in
    match uu____828 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____835;
          FStar_Syntax_Syntax.rng = uu____836;_}
        ->
        let uu____839 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____839
    | uu____840 ->
        (if w
         then
           (let uu____842 =
              let uu____847 =
                let uu____848 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____848  in
              (FStar_Errors.Warning_NotEmbedded, uu____847)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____842)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp 
let (e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding) =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng)
     in
  let unembed_env w t =
    let uu____878 =
      let uu____879 = FStar_Syntax_Subst.compress t  in
      uu____879.FStar_Syntax_Syntax.n  in
    match uu____878 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____885;
          FStar_Syntax_Syntax.rng = uu____886;_}
        ->
        let uu____889 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____889
    | uu____890 ->
        (if w
         then
           (let uu____892 =
              let uu____897 =
                let uu____898 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____898  in
              (FStar_Errors.Warning_NotEmbedded, uu____897)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____892)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_env unembed_env FStar_Reflection_Data.fstar_refl_env 
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
          let uu____919 =
            let uu____924 =
              let uu____925 =
                let uu____934 =
                  let uu____935 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____935  in
                FStar_Syntax_Syntax.as_arg uu____934  in
              [uu____925]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____924
             in
          uu____919 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____955 =
            let uu____960 =
              let uu____961 =
                let uu____970 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____970  in
              [uu____961]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____960
             in
          uu____955 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___230_989 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___230_989.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___230_989.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1008 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1008 with
    | (hd1,args) ->
        let uu____1053 =
          let uu____1068 =
            let uu____1069 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1069.FStar_Syntax_Syntax.n  in
          (uu____1068, args)  in
        (match uu____1053 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1143)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1178 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1178
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1187)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1222 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1222
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1229 ->
             (if w
              then
                (let uu____1245 =
                   let uu____1250 =
                     let uu____1251 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1251
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1250)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1245)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1259  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1272 =
            let uu____1277 =
              let uu____1278 =
                let uu____1287 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1287  in
              [uu____1278]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1277
             in
          uu____1272 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1312 =
            let uu____1317 =
              let uu____1318 =
                let uu____1327 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1327  in
              let uu____1328 =
                let uu____1339 =
                  let uu____1348 =
                    let uu____1349 =
                      let uu____1354 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1354  in
                    embed uu____1349 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1348  in
                [uu____1339]  in
              uu____1318 :: uu____1328  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1317
             in
          uu____1312 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1386 =
            let uu____1391 =
              let uu____1392 =
                let uu____1401 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1401  in
              [uu____1392]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1391
             in
          uu____1386 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1421 =
            let uu____1426 =
              let uu____1427 =
                let uu____1436 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1436  in
              [uu____1427]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1426
             in
          uu____1421 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1457 =
            let uu____1462 =
              let uu____1463 =
                let uu____1472 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1472  in
              let uu____1473 =
                let uu____1484 =
                  let uu____1493 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1493  in
                [uu____1484]  in
              uu____1463 :: uu____1473  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1462
             in
          uu____1457 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1536 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1536 with
      | (hd1,args) ->
          let uu____1581 =
            let uu____1594 =
              let uu____1595 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1595.FStar_Syntax_Syntax.n  in
            (uu____1594, args)  in
          (match uu____1581 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1610)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1635 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1635
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1644)::(ps,uu____1646)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1681 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1681
                 (fun f1  ->
                    let uu____1687 =
                      let uu____1692 =
                        let uu____1697 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1697  in
                      unembed' w uu____1692 ps  in
                    FStar_Util.bind_opt uu____1687
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1714)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1739 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1739
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1748)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1773 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1773
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1782)::(t2,uu____1784)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1819 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1819
                 (fun bv1  ->
                    let uu____1825 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1825
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1832 ->
               (if w
                then
                  (let uu____1846 =
                     let uu____1851 =
                       let uu____1852 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1852
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1851)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1846)
                else ();
                FStar_Pervasives_Native.None))
       in
    mk_emb embed_pattern unembed_pattern
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
    let uu____1871 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1871
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1885 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1885 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1907 =
            let uu____1912 =
              let uu____1913 =
                let uu____1922 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1922  in
              [uu____1913]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1912
             in
          uu____1907 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1942 =
            let uu____1947 =
              let uu____1948 =
                let uu____1957 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1957  in
              [uu____1948]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1947
             in
          uu____1942 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1977 =
            let uu____1982 =
              let uu____1983 =
                let uu____1992 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1992  in
              [uu____1983]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1982
             in
          uu____1977 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2013 =
            let uu____2018 =
              let uu____2019 =
                let uu____2028 =
                  let uu____2029 = e_term_aq aq  in embed uu____2029 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2028  in
              let uu____2032 =
                let uu____2043 =
                  let uu____2052 =
                    let uu____2053 = e_argv_aq aq  in embed uu____2053 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2052  in
                [uu____2043]  in
              uu____2019 :: uu____2032  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2018
             in
          uu____2013 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2092 =
            let uu____2097 =
              let uu____2098 =
                let uu____2107 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2107  in
              let uu____2108 =
                let uu____2119 =
                  let uu____2128 =
                    let uu____2129 = e_term_aq aq  in embed uu____2129 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2128  in
                [uu____2119]  in
              uu____2098 :: uu____2108  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2097
             in
          uu____2092 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2160 =
            let uu____2165 =
              let uu____2166 =
                let uu____2175 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2175  in
              let uu____2176 =
                let uu____2187 =
                  let uu____2196 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2196  in
                [uu____2187]  in
              uu____2166 :: uu____2176  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2165
             in
          uu____2160 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2224 =
            let uu____2229 =
              let uu____2230 =
                let uu____2239 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2239  in
              [uu____2230]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2229
             in
          uu____2224 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2260 =
            let uu____2265 =
              let uu____2266 =
                let uu____2275 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2275  in
              let uu____2276 =
                let uu____2287 =
                  let uu____2296 =
                    let uu____2297 = e_term_aq aq  in embed uu____2297 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2296  in
                [uu____2287]  in
              uu____2266 :: uu____2276  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2265
             in
          uu____2260 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2327 =
            let uu____2332 =
              let uu____2333 =
                let uu____2342 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2342  in
              [uu____2333]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2332
             in
          uu____2327 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2363 =
            let uu____2368 =
              let uu____2369 =
                let uu____2378 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2378  in
              let uu____2379 =
                let uu____2390 =
                  let uu____2399 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2399  in
                [uu____2390]  in
              uu____2369 :: uu____2379  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2368
             in
          uu____2363 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2434 =
            let uu____2439 =
              let uu____2440 =
                let uu____2449 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2449  in
              let uu____2450 =
                let uu____2461 =
                  let uu____2470 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2470  in
                let uu____2471 =
                  let uu____2482 =
                    let uu____2491 =
                      let uu____2492 = e_term_aq aq  in
                      embed uu____2492 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2491  in
                  let uu____2495 =
                    let uu____2506 =
                      let uu____2515 =
                        let uu____2516 = e_term_aq aq  in
                        embed uu____2516 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2515  in
                    [uu____2506]  in
                  uu____2482 :: uu____2495  in
                uu____2461 :: uu____2471  in
              uu____2440 :: uu____2450  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2439
             in
          uu____2434 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2567 =
            let uu____2572 =
              let uu____2573 =
                let uu____2582 =
                  let uu____2583 = e_term_aq aq  in embed uu____2583 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2582  in
              let uu____2586 =
                let uu____2597 =
                  let uu____2606 =
                    let uu____2607 =
                      let uu____2616 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2616  in
                    embed uu____2607 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2606  in
                [uu____2597]  in
              uu____2573 :: uu____2586  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2572
             in
          uu____2567 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2666 =
            let uu____2671 =
              let uu____2672 =
                let uu____2681 =
                  let uu____2682 = e_term_aq aq  in embed uu____2682 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2681  in
              let uu____2685 =
                let uu____2696 =
                  let uu____2705 =
                    let uu____2706 = e_term_aq aq  in embed uu____2706 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2705  in
                let uu____2709 =
                  let uu____2720 =
                    let uu____2729 =
                      let uu____2730 =
                        let uu____2735 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2735  in
                      embed uu____2730 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2729  in
                  [uu____2720]  in
                uu____2696 :: uu____2709  in
              uu____2672 :: uu____2685  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2671
             in
          uu____2666 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2781 =
            let uu____2786 =
              let uu____2787 =
                let uu____2796 =
                  let uu____2797 = e_term_aq aq  in embed uu____2797 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2796  in
              let uu____2800 =
                let uu____2811 =
                  let uu____2820 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2820  in
                let uu____2821 =
                  let uu____2832 =
                    let uu____2841 =
                      let uu____2842 =
                        let uu____2847 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2847  in
                      embed uu____2842 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2841  in
                  [uu____2832]  in
                uu____2811 :: uu____2821  in
              uu____2787 :: uu____2800  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2786
             in
          uu____2781 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___231_2886 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___231_2886.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___231_2886.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2902 = FStar_Syntax_Util.head_and_args t  in
      match uu____2902 with
      | (hd1,args) ->
          let uu____2947 =
            let uu____2960 =
              let uu____2961 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2961.FStar_Syntax_Syntax.n  in
            (uu____2960, args)  in
          (match uu____2947 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2976)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3001 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3001
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3010)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3035 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3035
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3044)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3069 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3069
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3078)::(r,uu____3080)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3115 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3115
                 (fun l1  ->
                    let uu____3121 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3121
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3130)::(t1,uu____3132)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3167 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3167
                 (fun b1  ->
                    let uu____3173 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3173
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3182)::(t1,uu____3184)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3219 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3219
                 (fun b1  ->
                    let uu____3225 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3225
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3234)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3259 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3259
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3268)::(t1,uu____3270)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3305 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3305
                 (fun b1  ->
                    let uu____3311 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3311
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3320)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3345 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3345
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3354)::(l,uu____3356)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3391 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3391
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3402)::(b,uu____3404)::(t1,uu____3406)::(t2,uu____3408)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3463 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3463
                 (fun r1  ->
                    let uu____3469 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3469
                      (fun b1  ->
                         let uu____3475 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3475
                           (fun t11  ->
                              let uu____3481 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3481
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3490)::(brs,uu____3492)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3527 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3527
                 (fun t2  ->
                    let uu____3533 =
                      let uu____3538 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3538 brs  in
                    FStar_Util.bind_opt uu____3533
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3557)::(t1,uu____3559)::(tacopt,uu____3561)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3606 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3606
                 (fun e1  ->
                    let uu____3612 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3612
                      (fun t2  ->
                         let uu____3618 =
                           let uu____3623 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3623 tacopt  in
                         FStar_Util.bind_opt uu____3618
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3642)::(c,uu____3644)::(tacopt,uu____3646)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3691 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3691
                 (fun e1  ->
                    let uu____3697 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3697
                      (fun c1  ->
                         let uu____3703 =
                           let uu____3708 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3708 tacopt  in
                         FStar_Util.bind_opt uu____3703
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
           | uu____3742 ->
               (if w
                then
                  (let uu____3756 =
                     let uu____3761 =
                       let uu____3762 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3762
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3761)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3756)
                else ();
                FStar_Pervasives_Native.None))
       in
    mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____3787 =
      let uu____3792 =
        let uu____3793 =
          let uu____3802 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3802  in
        let uu____3803 =
          let uu____3814 =
            let uu____3823 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3823  in
          let uu____3824 =
            let uu____3835 =
              let uu____3844 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____3844  in
            [uu____3835]  in
          uu____3814 :: uu____3824  in
        uu____3793 :: uu____3803  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3792
       in
    uu____3787 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3895 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3895 with
    | (hd1,args) ->
        let uu____3940 =
          let uu____3953 =
            let uu____3954 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3954.FStar_Syntax_Syntax.n  in
          (uu____3953, args)  in
        (match uu____3940 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3969)::(idx,uu____3971)::(s,uu____3973)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4018 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4018
               (fun nm1  ->
                  let uu____4024 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4024
                    (fun idx1  ->
                       let uu____4030 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4030
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4037 ->
             (if w
              then
                (let uu____4051 =
                   let uu____4056 =
                     let uu____4057 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4057
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4056)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4051)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding) =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____4078 =
          let uu____4083 =
            let uu____4084 =
              let uu____4093 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4093  in
            let uu____4094 =
              let uu____4105 =
                let uu____4114 =
                  let uu____4115 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4115 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4114  in
              [uu____4105]  in
            uu____4084 :: uu____4094  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4083
           in
        uu____4078 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4153 =
          let uu____4158 =
            let uu____4159 =
              let uu____4168 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4168  in
            let uu____4169 =
              let uu____4180 =
                let uu____4189 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4189  in
              [uu____4180]  in
            uu____4159 :: uu____4169  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4158
           in
        uu____4153 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___232_4216 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___232_4216.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___232_4216.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4233 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4233 with
    | (hd1,args) ->
        let uu____4278 =
          let uu____4291 =
            let uu____4292 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4292.FStar_Syntax_Syntax.n  in
          (uu____4291, args)  in
        (match uu____4278 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4307)::(md,uu____4309)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4344 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4344
               (fun t3  ->
                  let uu____4350 =
                    let uu____4355 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4355 md  in
                  FStar_Util.bind_opt uu____4350
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4374)::(post,uu____4376)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4411 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4411
               (fun pre1  ->
                  let uu____4417 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4417
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
         | uu____4441 ->
             (if w
              then
                (let uu____4455 =
                   let uu____4460 =
                     let uu____4461 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4461
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4460)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4455)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_comp_view unembed_comp_view
    FStar_Reflection_Data.fstar_refl_comp_view
  
let (e_order : FStar_Order.order FStar_Syntax_Embeddings.embedding) =
  let embed_order rng o =
    let r =
      match o with
      | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
      | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
      | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt  in
    let uu___233_4481 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___233_4481.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___233_4481.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4500 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4500 with
    | (hd1,args) ->
        let uu____4545 =
          let uu____4560 =
            let uu____4561 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4561.FStar_Syntax_Syntax.n  in
          (uu____4560, args)  in
        (match uu____4545 with
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
         | uu____4633 ->
             (if w
              then
                (let uu____4649 =
                   let uu____4654 =
                     let uu____4655 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4655
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4654)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4649)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_order unembed_order FStar_Syntax_Syntax.t_order 
let (e_sigelt : FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings.embedding)
  =
  let embed_sigelt rng se =
    FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng)
     in
  let unembed_sigelt w t =
    let uu____4685 =
      let uu____4686 = FStar_Syntax_Subst.compress t  in
      uu____4686.FStar_Syntax_Syntax.n  in
    match uu____4685 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____4692;
          FStar_Syntax_Syntax.rng = uu____4693;_}
        ->
        let uu____4696 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4696
    | uu____4697 ->
        (if w
         then
           (let uu____4699 =
              let uu____4704 =
                let uu____4705 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4705
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4704)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4699)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____4758 uu____4759 =
    let uu____4781 =
      let uu____4786 = FStar_Ident.range_of_id i  in
      let uu____4787 = FStar_Ident.text_of_id i  in (uu____4786, uu____4787)
       in
    embed repr rng uu____4781  in
  let unembed_ident t w uu____4811 =
    let uu____4816 = unembed' w repr t  in
    match uu____4816 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4835 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4835
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____4840 =
    FStar_Syntax_Syntax.t_tuple2_of FStar_Syntax_Syntax.t_range
      FStar_Syntax_Syntax.t_string
     in
  let uu____4841 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident uu____4840
    FStar_Ident.text_of_id uu____4841
  
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
        let uu____4874 =
          let uu____4879 =
            let uu____4880 =
              let uu____4889 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____4889  in
            let uu____4890 =
              let uu____4901 =
                let uu____4910 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____4910  in
              let uu____4911 =
                let uu____4922 =
                  let uu____4931 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____4931  in
                let uu____4934 =
                  let uu____4945 =
                    let uu____4954 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____4954  in
                  let uu____4955 =
                    let uu____4966 =
                      let uu____4975 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____4975  in
                    [uu____4966]  in
                  uu____4945 :: uu____4955  in
                uu____4922 :: uu____4934  in
              uu____4901 :: uu____4911  in
            uu____4880 :: uu____4890  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4879
           in
        uu____4874 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5028 =
          let uu____5033 =
            let uu____5034 =
              let uu____5043 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5043  in
            let uu____5046 =
              let uu____5057 =
                let uu____5066 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5066  in
              [uu____5057]  in
            uu____5034 :: uu____5046  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5033
           in
        uu____5028 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5110 =
          let uu____5115 =
            let uu____5116 =
              let uu____5125 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5125  in
            let uu____5128 =
              let uu____5139 =
                let uu____5148 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5148  in
              let uu____5151 =
                let uu____5162 =
                  let uu____5171 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5171  in
                let uu____5172 =
                  let uu____5183 =
                    let uu____5192 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5192  in
                  let uu____5193 =
                    let uu____5204 =
                      let uu____5213 =
                        let uu____5214 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5214 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5213  in
                    [uu____5204]  in
                  uu____5183 :: uu____5193  in
                uu____5162 :: uu____5172  in
              uu____5139 :: uu____5151  in
            uu____5116 :: uu____5128  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5115
           in
        uu____5110 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___234_5277 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___234_5277.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___234_5277.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5294 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5294 with
    | (hd1,args) ->
        let uu____5339 =
          let uu____5352 =
            let uu____5353 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5353.FStar_Syntax_Syntax.n  in
          (uu____5352, args)  in
        (match uu____5339 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5368)::(us,uu____5370)::(bs,uu____5372)::(t2,uu____5374)::
            (dcs,uu____5376)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5441 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5441
               (fun nm1  ->
                  let uu____5455 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5455
                    (fun us1  ->
                       let uu____5469 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5469
                         (fun bs1  ->
                            let uu____5475 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5475
                              (fun t3  ->
                                 let uu____5481 =
                                   let uu____5488 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5488 dcs  in
                                 FStar_Util.bind_opt uu____5481
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_42  ->
                                           FStar_Pervasives_Native.Some _0_42)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5521)::(fvar1,uu____5523)::(univs1,uu____5525)::
            (ty,uu____5527)::(t2,uu____5529)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5594 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5594
               (fun r1  ->
                  let uu____5600 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5600
                    (fun fvar2  ->
                       let uu____5606 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5606
                         (fun univs2  ->
                            let uu____5620 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____5620
                              (fun ty1  ->
                                 let uu____5626 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____5626
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
         | uu____5650 ->
             (if w
              then
                (let uu____5664 =
                   let uu____5669 =
                     let uu____5670 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5670
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5669)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5664)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_Data.fstar_refl_sigelt_view
  
let (e_exp : FStar_Reflection_Data.exp FStar_Syntax_Embeddings.embedding) =
  let rec embed_exp rng e =
    let r =
      match e with
      | FStar_Reflection_Data.Unit  ->
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Var i ->
          let uu____5691 =
            let uu____5696 =
              let uu____5697 =
                let uu____5706 =
                  let uu____5707 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5707  in
                FStar_Syntax_Syntax.as_arg uu____5706  in
              [uu____5697]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5696
             in
          uu____5691 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5728 =
            let uu____5733 =
              let uu____5734 =
                let uu____5743 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5743  in
              let uu____5744 =
                let uu____5755 =
                  let uu____5764 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5764  in
                [uu____5755]  in
              uu____5734 :: uu____5744  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5733
             in
          uu____5728 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___235_5791 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___235_5791.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___235_5791.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5810 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5810 with
    | (hd1,args) ->
        let uu____5855 =
          let uu____5868 =
            let uu____5869 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5869.FStar_Syntax_Syntax.n  in
          (uu____5868, args)  in
        (match uu____5855 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5899)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5924 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____5924
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____5933)::(e2,uu____5935)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____5970 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____5970
               (fun e11  ->
                  let uu____5976 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____5976
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____5983 ->
             (if w
              then
                (let uu____5997 =
                   let uu____6002 =
                     let uu____6003 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6003
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6002)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5997)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp 
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
    let uu____6019 =
      let uu____6024 =
        let uu____6025 =
          let uu____6034 =
            let uu____6035 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____6035  in
          FStar_Syntax_Syntax.as_arg uu____6034  in
        [uu____6025]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____6024
       in
    uu____6019 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6060 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____6060 with
    | (bv,aq) ->
        let uu____6067 =
          let uu____6072 =
            let uu____6073 =
              let uu____6082 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____6082  in
            let uu____6083 =
              let uu____6094 =
                let uu____6103 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____6103  in
              [uu____6094]  in
            uu____6073 :: uu____6083  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____6072
           in
        uu____6067 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6136 =
      let uu____6141 =
        let uu____6142 =
          let uu____6151 =
            let uu____6152 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____6157 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____6152 i.FStar_Syntax_Syntax.rng uu____6157  in
          FStar_Syntax_Syntax.as_arg uu____6151  in
        [uu____6142]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____6141
       in
    uu____6136 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6186 =
      let uu____6191 =
        let uu____6192 =
          let uu____6201 =
            let uu____6202 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____6202  in
          FStar_Syntax_Syntax.as_arg uu____6201  in
        [uu____6192]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____6191
       in
    uu____6186 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6232 =
      let uu____6237 =
        let uu____6238 =
          let uu____6247 =
            let uu____6248 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____6248  in
          FStar_Syntax_Syntax.as_arg uu____6247  in
        [uu____6238]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6237
       in
    uu____6232 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  