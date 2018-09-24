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
            (fun uu____422  ->
               match uu____422 with
               | (bv,e) ->
                   let uu____431 = unembed_term w e  in
                   FStar_Util.bind_opt uu____431
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____409
          (fun s  ->
             let uu____445 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____445)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____447 =
        let uu____448 = FStar_Syntax_Subst.compress t1  in
        uu____448.FStar_Syntax_Syntax.n  in
      match uu____447 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____459 ->
          (if w
           then
             (let uu____461 =
                let uu____466 =
                  let uu____467 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____467  in
                (FStar_Errors.Warning_NotEmbedded, uu____466)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____461)
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
          let uu____496 =
            let uu____501 =
              let uu____502 =
                let uu____511 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____511  in
              [uu____502]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____501
             in
          uu____496 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___236_530 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___236_530.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___236_530.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____549 = FStar_Syntax_Util.head_and_args t1  in
    match uu____549 with
    | (hd1,args) ->
        let uu____594 =
          let uu____609 =
            let uu____610 = FStar_Syntax_Util.un_uinst hd1  in
            uu____610.FStar_Syntax_Syntax.n  in
          (uu____609, args)  in
        (match uu____594 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____665)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____700 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____700
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____705 ->
             (if w
              then
                (let uu____721 =
                   let uu____726 =
                     let uu____727 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____727
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____726)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____721)
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
    let uu____759 =
      let uu____760 = FStar_Syntax_Subst.compress t  in
      uu____760.FStar_Syntax_Syntax.n  in
    match uu____759 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____766;
          FStar_Syntax_Syntax.rng = uu____767;_}
        ->
        let uu____770 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____770
    | uu____771 ->
        (if w
         then
           (let uu____773 =
              let uu____778 =
                let uu____779 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____779  in
              (FStar_Errors.Warning_NotEmbedded, uu____778)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____773)
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
    let uu____809 =
      let uu____810 = FStar_Syntax_Subst.compress t  in
      uu____810.FStar_Syntax_Syntax.n  in
    match uu____809 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____816;
          FStar_Syntax_Syntax.rng = uu____817;_}
        ->
        let uu____820 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____820
    | uu____821 ->
        (if w
         then
           (let uu____823 =
              let uu____828 =
                let uu____829 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____829  in
              (FStar_Errors.Warning_NotEmbedded, uu____828)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____823)
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
    let uu____859 =
      let uu____860 = FStar_Syntax_Subst.compress t  in
      uu____860.FStar_Syntax_Syntax.n  in
    match uu____859 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____866;
          FStar_Syntax_Syntax.rng = uu____867;_}
        ->
        let uu____870 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____870
    | uu____871 ->
        (if w
         then
           (let uu____873 =
              let uu____878 =
                let uu____879 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____879  in
              (FStar_Errors.Warning_NotEmbedded, uu____878)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____873)
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
          let uu____900 =
            let uu____905 =
              let uu____906 =
                let uu____915 =
                  let uu____916 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____916  in
                FStar_Syntax_Syntax.as_arg uu____915  in
              [uu____906]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____905
             in
          uu____900 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____936 =
            let uu____941 =
              let uu____942 =
                let uu____951 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____951  in
              [uu____942]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____941
             in
          uu____936 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____971 =
            let uu____976 =
              let uu____977 =
                let uu____986 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____986  in
              [uu____977]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____976
             in
          uu____971 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___237_1005 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___237_1005.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___237_1005.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1024 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1024 with
    | (hd1,args) ->
        let uu____1069 =
          let uu____1084 =
            let uu____1085 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1085.FStar_Syntax_Syntax.n  in
          (uu____1084, args)  in
        (match uu____1069 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1159)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1194 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1194
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1203)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1238 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1238
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____1247)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1282 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____1282
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _0_3  -> FStar_Pervasives_Native.Some _0_3)
                    (FStar_Reflection_Data.C_Range r1))
         | uu____1289 ->
             (if w
              then
                (let uu____1305 =
                   let uu____1310 =
                     let uu____1311 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1311
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1310)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1305)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1319  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1332 =
            let uu____1337 =
              let uu____1338 =
                let uu____1347 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1347  in
              [uu____1338]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1337
             in
          uu____1332 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1372 =
            let uu____1377 =
              let uu____1378 =
                let uu____1387 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1387  in
              let uu____1388 =
                let uu____1399 =
                  let uu____1408 =
                    let uu____1409 =
                      let uu____1414 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1414  in
                    embed uu____1409 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1408  in
                [uu____1399]  in
              uu____1378 :: uu____1388  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1377
             in
          uu____1372 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1446 =
            let uu____1451 =
              let uu____1452 =
                let uu____1461 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1461  in
              [uu____1452]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1451
             in
          uu____1446 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1481 =
            let uu____1486 =
              let uu____1487 =
                let uu____1496 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1496  in
              [uu____1487]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1486
             in
          uu____1481 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1517 =
            let uu____1522 =
              let uu____1523 =
                let uu____1532 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1532  in
              let uu____1533 =
                let uu____1544 =
                  let uu____1553 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1553  in
                [uu____1544]  in
              uu____1523 :: uu____1533  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1522
             in
          uu____1517 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1596 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1596 with
      | (hd1,args) ->
          let uu____1641 =
            let uu____1654 =
              let uu____1655 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1655.FStar_Syntax_Syntax.n  in
            (uu____1654, args)  in
          (match uu____1641 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1670)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1695 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1695
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_Pervasives_Native.Some _0_4)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1704)::(ps,uu____1706)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1741 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1741
                 (fun f1  ->
                    let uu____1747 =
                      let uu____1752 =
                        let uu____1757 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1757  in
                      unembed' w uu____1752 ps  in
                    FStar_Util.bind_opt uu____1747
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_5  -> FStar_Pervasives_Native.Some _0_5)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1774)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1799 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1799
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_6  -> FStar_Pervasives_Native.Some _0_6)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1808)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1833 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1833
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_7  -> FStar_Pervasives_Native.Some _0_7)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1842)::(t2,uu____1844)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1879 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1879
                 (fun bv1  ->
                    let uu____1885 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1885
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_8  -> FStar_Pervasives_Native.Some _0_8)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1892 ->
               (if w
                then
                  (let uu____1906 =
                     let uu____1911 =
                       let uu____1912 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1912
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1911)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1906)
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
    let uu____1931 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1931
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1945 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1945 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1967 =
            let uu____1972 =
              let uu____1973 =
                let uu____1982 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1982  in
              [uu____1973]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1972
             in
          uu____1967 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2002 =
            let uu____2007 =
              let uu____2008 =
                let uu____2017 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2017  in
              [uu____2008]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2007
             in
          uu____2002 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2037 =
            let uu____2042 =
              let uu____2043 =
                let uu____2052 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2052  in
              [uu____2043]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2042
             in
          uu____2037 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2073 =
            let uu____2078 =
              let uu____2079 =
                let uu____2088 =
                  let uu____2089 = e_term_aq aq  in embed uu____2089 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2088  in
              let uu____2092 =
                let uu____2103 =
                  let uu____2112 =
                    let uu____2113 = e_argv_aq aq  in embed uu____2113 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2112  in
                [uu____2103]  in
              uu____2079 :: uu____2092  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2078
             in
          uu____2073 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2152 =
            let uu____2157 =
              let uu____2158 =
                let uu____2167 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2167  in
              let uu____2168 =
                let uu____2179 =
                  let uu____2188 =
                    let uu____2189 = e_term_aq aq  in embed uu____2189 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2188  in
                [uu____2179]  in
              uu____2158 :: uu____2168  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2157
             in
          uu____2152 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2220 =
            let uu____2225 =
              let uu____2226 =
                let uu____2235 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2235  in
              let uu____2236 =
                let uu____2247 =
                  let uu____2256 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2256  in
                [uu____2247]  in
              uu____2226 :: uu____2236  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2225
             in
          uu____2220 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2284 =
            let uu____2289 =
              let uu____2290 =
                let uu____2299 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2299  in
              [uu____2290]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2289
             in
          uu____2284 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2320 =
            let uu____2325 =
              let uu____2326 =
                let uu____2335 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2335  in
              let uu____2336 =
                let uu____2347 =
                  let uu____2356 =
                    let uu____2357 = e_term_aq aq  in embed uu____2357 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2356  in
                [uu____2347]  in
              uu____2326 :: uu____2336  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2325
             in
          uu____2320 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2387 =
            let uu____2392 =
              let uu____2393 =
                let uu____2402 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2402  in
              [uu____2393]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2392
             in
          uu____2387 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2423 =
            let uu____2428 =
              let uu____2429 =
                let uu____2438 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2438  in
              let uu____2439 =
                let uu____2450 =
                  let uu____2459 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2459  in
                [uu____2450]  in
              uu____2429 :: uu____2439  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2428
             in
          uu____2423 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2494 =
            let uu____2499 =
              let uu____2500 =
                let uu____2509 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2509  in
              let uu____2510 =
                let uu____2521 =
                  let uu____2530 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2530  in
                let uu____2531 =
                  let uu____2542 =
                    let uu____2551 =
                      let uu____2552 = e_term_aq aq  in
                      embed uu____2552 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2551  in
                  let uu____2555 =
                    let uu____2566 =
                      let uu____2575 =
                        let uu____2576 = e_term_aq aq  in
                        embed uu____2576 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2575  in
                    [uu____2566]  in
                  uu____2542 :: uu____2555  in
                uu____2521 :: uu____2531  in
              uu____2500 :: uu____2510  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2499
             in
          uu____2494 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2627 =
            let uu____2632 =
              let uu____2633 =
                let uu____2642 =
                  let uu____2643 = e_term_aq aq  in embed uu____2643 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2642  in
              let uu____2646 =
                let uu____2657 =
                  let uu____2666 =
                    let uu____2667 =
                      let uu____2676 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2676  in
                    embed uu____2667 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2666  in
                [uu____2657]  in
              uu____2633 :: uu____2646  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2632
             in
          uu____2627 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2726 =
            let uu____2731 =
              let uu____2732 =
                let uu____2741 =
                  let uu____2742 = e_term_aq aq  in embed uu____2742 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2741  in
              let uu____2745 =
                let uu____2756 =
                  let uu____2765 =
                    let uu____2766 = e_term_aq aq  in embed uu____2766 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2765  in
                let uu____2769 =
                  let uu____2780 =
                    let uu____2789 =
                      let uu____2790 =
                        let uu____2795 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2795  in
                      embed uu____2790 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2789  in
                  [uu____2780]  in
                uu____2756 :: uu____2769  in
              uu____2732 :: uu____2745  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2731
             in
          uu____2726 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2841 =
            let uu____2846 =
              let uu____2847 =
                let uu____2856 =
                  let uu____2857 = e_term_aq aq  in embed uu____2857 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2856  in
              let uu____2860 =
                let uu____2871 =
                  let uu____2880 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2880  in
                let uu____2881 =
                  let uu____2892 =
                    let uu____2901 =
                      let uu____2902 =
                        let uu____2907 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2907  in
                      embed uu____2902 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2901  in
                  [uu____2892]  in
                uu____2871 :: uu____2881  in
              uu____2847 :: uu____2860  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2846
             in
          uu____2841 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___238_2946 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___238_2946.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___238_2946.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2962 = FStar_Syntax_Util.head_and_args t  in
      match uu____2962 with
      | (hd1,args) ->
          let uu____3007 =
            let uu____3020 =
              let uu____3021 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3021.FStar_Syntax_Syntax.n  in
            (uu____3020, args)  in
          (match uu____3007 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3036)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3061 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3061
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_9  -> FStar_Pervasives_Native.Some _0_9)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3070)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3095 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3095
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_10  -> FStar_Pervasives_Native.Some _0_10)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3104)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3129 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3129
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_11  -> FStar_Pervasives_Native.Some _0_11)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3138)::(r,uu____3140)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3175 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3175
                 (fun l1  ->
                    let uu____3181 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3181
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_12  -> FStar_Pervasives_Native.Some _0_12)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3190)::(t1,uu____3192)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3227 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3227
                 (fun b1  ->
                    let uu____3233 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3233
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_13  -> FStar_Pervasives_Native.Some _0_13)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3242)::(t1,uu____3244)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3279 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3279
                 (fun b1  ->
                    let uu____3285 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3285
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3294)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3319 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3319
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3328)::(t1,uu____3330)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3365 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3365
                 (fun b1  ->
                    let uu____3371 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3371
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3380)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3405 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3405
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3414)::(l,uu____3416)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3451 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3451
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3462)::(b,uu____3464)::(t1,uu____3466)::(t2,uu____3468)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3523 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3523
                 (fun r1  ->
                    let uu____3529 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3529
                      (fun b1  ->
                         let uu____3535 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3535
                           (fun t11  ->
                              let uu____3541 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3541
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_19  ->
                                        FStar_Pervasives_Native.Some _0_19)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3550)::(brs,uu____3552)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3587 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3587
                 (fun t2  ->
                    let uu____3593 =
                      let uu____3598 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3598 brs  in
                    FStar_Util.bind_opt uu____3593
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3617)::(t1,uu____3619)::(tacopt,uu____3621)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3666 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3666
                 (fun e1  ->
                    let uu____3672 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3672
                      (fun t2  ->
                         let uu____3678 =
                           let uu____3683 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3683 tacopt  in
                         FStar_Util.bind_opt uu____3678
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_21  ->
                                   FStar_Pervasives_Native.Some _0_21)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3702)::(c,uu____3704)::(tacopt,uu____3706)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3751 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3751
                 (fun e1  ->
                    let uu____3757 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3757
                      (fun c1  ->
                         let uu____3763 =
                           let uu____3768 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3768 tacopt  in
                         FStar_Util.bind_opt uu____3763
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_22  ->
                                   FStar_Pervasives_Native.Some _0_22)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____3802 ->
               (if w
                then
                  (let uu____3816 =
                     let uu____3821 =
                       let uu____3822 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3822
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3821)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3816)
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
    let uu____3845 =
      let uu____3850 =
        let uu____3851 =
          let uu____3860 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3860  in
        let uu____3861 =
          let uu____3872 =
            let uu____3881 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3881  in
          let uu____3882 =
            let uu____3893 =
              let uu____3902 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____3902  in
            [uu____3893]  in
          uu____3872 :: uu____3882  in
        uu____3851 :: uu____3861  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3850
       in
    uu____3845 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3953 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3953 with
    | (hd1,args) ->
        let uu____3998 =
          let uu____4011 =
            let uu____4012 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4012.FStar_Syntax_Syntax.n  in
          (uu____4011, args)  in
        (match uu____3998 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4027)::(idx,uu____4029)::(s,uu____4031)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4076 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4076
               (fun nm1  ->
                  let uu____4082 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4082
                    (fun idx1  ->
                       let uu____4088 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4088
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_24  ->
                                 FStar_Pervasives_Native.Some _0_24)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4095 ->
             (if w
              then
                (let uu____4109 =
                   let uu____4114 =
                     let uu____4115 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4115
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4114)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4109)
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
        let uu____4136 =
          let uu____4141 =
            let uu____4142 =
              let uu____4151 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4151  in
            let uu____4152 =
              let uu____4163 =
                let uu____4172 =
                  let uu____4173 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4173 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4172  in
              [uu____4163]  in
            uu____4142 :: uu____4152  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4141
           in
        uu____4136 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4211 =
          let uu____4216 =
            let uu____4217 =
              let uu____4226 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4226  in
            let uu____4227 =
              let uu____4238 =
                let uu____4247 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4247  in
              [uu____4238]  in
            uu____4217 :: uu____4227  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4216
           in
        uu____4211 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___239_4274 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___239_4274.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___239_4274.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4291 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4291 with
    | (hd1,args) ->
        let uu____4336 =
          let uu____4349 =
            let uu____4350 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4350.FStar_Syntax_Syntax.n  in
          (uu____4349, args)  in
        (match uu____4336 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4365)::(md,uu____4367)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4402 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4402
               (fun t3  ->
                  let uu____4408 =
                    let uu____4413 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4413 md  in
                  FStar_Util.bind_opt uu____4408
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4432)::(post,uu____4434)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4469 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4469
               (fun pre1  ->
                  let uu____4475 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4475
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
               FStar_Reflection_Data.C_Unknown
         | uu____4499 ->
             (if w
              then
                (let uu____4513 =
                   let uu____4518 =
                     let uu____4519 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4519
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4518)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4513)
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
    let uu___240_4539 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___240_4539.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___240_4539.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4558 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4558 with
    | (hd1,args) ->
        let uu____4603 =
          let uu____4618 =
            let uu____4619 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4619.FStar_Syntax_Syntax.n  in
          (uu____4618, args)  in
        (match uu____4603 with
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
         | uu____4691 ->
             (if w
              then
                (let uu____4707 =
                   let uu____4712 =
                     let uu____4713 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4713
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4712)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4707)
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
    let uu____4743 =
      let uu____4744 = FStar_Syntax_Subst.compress t  in
      uu____4744.FStar_Syntax_Syntax.n  in
    match uu____4743 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____4750;
          FStar_Syntax_Syntax.rng = uu____4751;_}
        ->
        let uu____4754 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4754
    | uu____4755 ->
        (if w
         then
           (let uu____4757 =
              let uu____4762 =
                let uu____4763 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4763
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4762)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4757)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____4816 uu____4817 =
    let uu____4839 =
      let uu____4844 = FStar_Ident.range_of_id i  in
      let uu____4845 = FStar_Ident.text_of_id i  in (uu____4844, uu____4845)
       in
    embed repr rng uu____4839  in
  let unembed_ident t w uu____4869 =
    let uu____4874 = unembed' w repr t  in
    match uu____4874 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4893 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4893
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____4898 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____4898
  
let (e_univ_name :
  FStar_Syntax_Syntax.univ_name FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.set_type FStar_Reflection_Data.fstar_refl_univ_name
    e_ident
  
let (e_univ_names :
  FStar_Syntax_Syntax.univ_name Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_univ_name 
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,univs1,ty,t) ->
        let uu____4931 =
          let uu____4936 =
            let uu____4937 =
              let uu____4946 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____4946  in
            let uu____4947 =
              let uu____4958 =
                let uu____4967 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____4967  in
              let uu____4968 =
                let uu____4979 =
                  let uu____4988 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____4988  in
                let uu____4991 =
                  let uu____5002 =
                    let uu____5011 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5011  in
                  let uu____5012 =
                    let uu____5023 =
                      let uu____5032 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5032  in
                    [uu____5023]  in
                  uu____5002 :: uu____5012  in
                uu____4979 :: uu____4991  in
              uu____4958 :: uu____4968  in
            uu____4937 :: uu____4947  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4936
           in
        uu____4931 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5085 =
          let uu____5090 =
            let uu____5091 =
              let uu____5100 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5100  in
            let uu____5103 =
              let uu____5114 =
                let uu____5123 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5123  in
              [uu____5114]  in
            uu____5091 :: uu____5103  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5090
           in
        uu____5085 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5167 =
          let uu____5172 =
            let uu____5173 =
              let uu____5182 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5182  in
            let uu____5185 =
              let uu____5196 =
                let uu____5205 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5205  in
              let uu____5208 =
                let uu____5219 =
                  let uu____5228 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5228  in
                let uu____5229 =
                  let uu____5240 =
                    let uu____5249 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5249  in
                  let uu____5250 =
                    let uu____5261 =
                      let uu____5270 =
                        let uu____5271 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5271 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5270  in
                    [uu____5261]  in
                  uu____5240 :: uu____5250  in
                uu____5219 :: uu____5229  in
              uu____5196 :: uu____5208  in
            uu____5173 :: uu____5185  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5172
           in
        uu____5167 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___241_5334 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___241_5334.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___241_5334.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5351 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5351 with
    | (hd1,args) ->
        let uu____5396 =
          let uu____5409 =
            let uu____5410 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5410.FStar_Syntax_Syntax.n  in
          (uu____5409, args)  in
        (match uu____5396 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5425)::(us,uu____5427)::(bs,uu____5429)::(t2,uu____5431)::
            (dcs,uu____5433)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5498 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5498
               (fun nm1  ->
                  let uu____5512 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5512
                    (fun us1  ->
                       let uu____5526 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5526
                         (fun bs1  ->
                            let uu____5532 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5532
                              (fun t3  ->
                                 let uu____5538 =
                                   let uu____5545 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5545 dcs  in
                                 FStar_Util.bind_opt uu____5538
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_28  ->
                                           FStar_Pervasives_Native.Some _0_28)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5578)::(fvar1,uu____5580)::(univs1,uu____5582)::
            (ty,uu____5584)::(t2,uu____5586)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5651 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5651
               (fun r1  ->
                  let uu____5657 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5657
                    (fun fvar2  ->
                       let uu____5663 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5663
                         (fun univs2  ->
                            let uu____5677 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____5677
                              (fun ty1  ->
                                 let uu____5683 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____5683
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _0_29  ->
                                           FStar_Pervasives_Native.Some _0_29)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____5707 ->
             (if w
              then
                (let uu____5721 =
                   let uu____5726 =
                     let uu____5727 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5727
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5726)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5721)
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
          let uu____5748 =
            let uu____5753 =
              let uu____5754 =
                let uu____5763 =
                  let uu____5764 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5764  in
                FStar_Syntax_Syntax.as_arg uu____5763  in
              [uu____5754]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5753
             in
          uu____5748 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5785 =
            let uu____5790 =
              let uu____5791 =
                let uu____5800 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5800  in
              let uu____5801 =
                let uu____5812 =
                  let uu____5821 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5821  in
                [uu____5812]  in
              uu____5791 :: uu____5801  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5790
             in
          uu____5785 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___242_5848 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___242_5848.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___242_5848.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5867 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5867 with
    | (hd1,args) ->
        let uu____5912 =
          let uu____5925 =
            let uu____5926 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5926.FStar_Syntax_Syntax.n  in
          (uu____5925, args)  in
        (match uu____5912 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5956)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5981 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____5981
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____5990)::(e2,uu____5992)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6027 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6027
               (fun e11  ->
                  let uu____6033 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6033
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6040 ->
             (if w
              then
                (let uu____6054 =
                   let uu____6059 =
                     let uu____6060 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6060
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6059)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6054)
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
    let uu____6076 =
      let uu____6081 =
        let uu____6082 =
          let uu____6091 =
            let uu____6092 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____6092  in
          FStar_Syntax_Syntax.as_arg uu____6091  in
        [uu____6082]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____6081
       in
    uu____6076 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6117 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____6117 with
    | (bv,aq) ->
        let uu____6124 =
          let uu____6129 =
            let uu____6130 =
              let uu____6139 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____6139  in
            let uu____6140 =
              let uu____6151 =
                let uu____6160 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____6160  in
              [uu____6151]  in
            uu____6130 :: uu____6140  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____6129
           in
        uu____6124 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6193 =
      let uu____6198 =
        let uu____6199 =
          let uu____6208 =
            let uu____6209 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____6214 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____6209 i.FStar_Syntax_Syntax.rng uu____6214  in
          FStar_Syntax_Syntax.as_arg uu____6208  in
        [uu____6199]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____6198
       in
    uu____6193 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6243 =
      let uu____6248 =
        let uu____6249 =
          let uu____6258 =
            let uu____6259 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____6259  in
          FStar_Syntax_Syntax.as_arg uu____6258  in
        [uu____6249]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____6248
       in
    uu____6243 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6289 =
      let uu____6294 =
        let uu____6295 =
          let uu____6304 =
            let uu____6305 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____6305  in
          FStar_Syntax_Syntax.as_arg uu____6304  in
        [uu____6295]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6294
       in
    uu____6289 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  