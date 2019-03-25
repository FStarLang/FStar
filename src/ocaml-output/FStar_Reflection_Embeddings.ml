open Prims
let mk_emb :
  'Auu____8 .
    (FStar_Range.range -> 'Auu____8 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'Auu____8 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____8 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____52 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____52
  
let embed :
  'Auu____79 .
    'Auu____79 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____79 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____99 = FStar_Syntax_Embeddings.embed e x  in
        uu____99 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____117 .
    Prims.bool ->
      'Auu____117 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____117 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____141 = FStar_Syntax_Embeddings.unembed e x  in
        uu____141 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____179 =
      let uu____180 = FStar_Syntax_Subst.compress t  in
      uu____180.FStar_Syntax_Syntax.n  in
    match uu____179 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____186;
          FStar_Syntax_Syntax.rng = uu____187;_}
        ->
        let uu____190 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____190
    | uu____191 ->
        (if w
         then
           (let uu____194 =
              let uu____200 =
                let uu____202 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____202  in
              (FStar_Errors.Warning_NotEmbedded, uu____200)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____194)
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
    let uu____239 =
      let uu____240 = FStar_Syntax_Subst.compress t  in
      uu____240.FStar_Syntax_Syntax.n  in
    match uu____239 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____246;
          FStar_Syntax_Syntax.rng = uu____247;_}
        ->
        let uu____250 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____250
    | uu____251 ->
        (if w
         then
           (let uu____254 =
              let uu____260 =
                let uu____262 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____262  in
              (FStar_Errors.Warning_NotEmbedded, uu____260)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____254)
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
          let uu____314 = f x  in
          FStar_Util.bind_opt uu____314
            (fun x1  ->
               let uu____322 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____322
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
        let uu____391 =
          mapM_opt
            (fun uu____404  ->
               match uu____404 with
               | (bv,e) ->
                   let uu____413 = unembed_term w e  in
                   FStar_Util.bind_opt uu____413
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____391
          (fun s  ->
             let uu____427 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____427)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____429 =
        let uu____430 = FStar_Syntax_Subst.compress t1  in
        uu____430.FStar_Syntax_Syntax.n  in
      match uu____429 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____441 ->
          (if w
           then
             (let uu____444 =
                let uu____450 =
                  let uu____452 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____452  in
                (FStar_Errors.Warning_NotEmbedded, uu____450)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____444)
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
          let uu____487 =
            let uu____492 =
              let uu____493 =
                let uu____502 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____502  in
              [uu____493]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____492
             in
          uu____487 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___88_519 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___88_519.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___88_519.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____540 = FStar_Syntax_Util.head_and_args t1  in
    match uu____540 with
    | (hd1,args) ->
        let uu____585 =
          let uu____600 =
            let uu____601 = FStar_Syntax_Util.un_uinst hd1  in
            uu____601.FStar_Syntax_Syntax.n  in
          (uu____600, args)  in
        (match uu____585 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____656)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____691 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____691
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____696 ->
             (if w
              then
                (let uu____713 =
                   let uu____719 =
                     let uu____721 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____721
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____719)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____713)
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
    let uu____761 =
      let uu____762 = FStar_Syntax_Subst.compress t  in
      uu____762.FStar_Syntax_Syntax.n  in
    match uu____761 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____768;
          FStar_Syntax_Syntax.rng = uu____769;_}
        ->
        let uu____772 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____772
    | uu____773 ->
        (if w
         then
           (let uu____776 =
              let uu____782 =
                let uu____784 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____784  in
              (FStar_Errors.Warning_NotEmbedded, uu____782)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____776)
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
    let uu____821 =
      let uu____822 = FStar_Syntax_Subst.compress t  in
      uu____822.FStar_Syntax_Syntax.n  in
    match uu____821 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____828;
          FStar_Syntax_Syntax.rng = uu____829;_}
        ->
        let uu____832 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____832
    | uu____833 ->
        (if w
         then
           (let uu____836 =
              let uu____842 =
                let uu____844 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____844  in
              (FStar_Errors.Warning_NotEmbedded, uu____842)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____836)
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
    let uu____881 =
      let uu____882 = FStar_Syntax_Subst.compress t  in
      uu____882.FStar_Syntax_Syntax.n  in
    match uu____881 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____888;
          FStar_Syntax_Syntax.rng = uu____889;_}
        ->
        let uu____892 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____892
    | uu____893 ->
        (if w
         then
           (let uu____896 =
              let uu____902 =
                let uu____904 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____904  in
              (FStar_Errors.Warning_NotEmbedded, uu____902)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____896)
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
          let uu____930 =
            let uu____935 =
              let uu____936 =
                let uu____945 =
                  let uu____946 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____946  in
                FStar_Syntax_Syntax.as_arg uu____945  in
              [uu____936]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____935
             in
          uu____930 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____966 =
            let uu____971 =
              let uu____972 =
                let uu____981 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____981  in
              [uu____972]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____971
             in
          uu____966 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____1000 =
            let uu____1005 =
              let uu____1006 =
                let uu____1015 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1015  in
              [uu____1006]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____1005
             in
          uu____1000 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____1033 =
            let uu____1038 =
              let uu____1039 =
                let uu____1048 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____1048  in
              [uu____1039]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____1038
             in
          uu____1033 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___177_1068 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___177_1068.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___177_1068.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1089 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1089 with
    | (hd1,args) ->
        let uu____1134 =
          let uu____1149 =
            let uu____1150 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1150.FStar_Syntax_Syntax.n  in
          (uu____1149, args)  in
        (match uu____1134 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1224)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1259 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1259
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _1266  -> FStar_Pervasives_Native.Some _1266)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1269)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1304 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1304
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _1315  -> FStar_Pervasives_Native.Some _1315)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____1318)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1353 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____1353
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _1360  -> FStar_Pervasives_Native.Some _1360)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _1382  -> FStar_Pervasives_Native.Some _1382)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____1385)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____1420 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____1420
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _1439  -> FStar_Pervasives_Native.Some _1439)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____1440 ->
             (if w
              then
                (let uu____1457 =
                   let uu____1463 =
                     let uu____1465 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1465
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1463)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1457)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1478  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1491 =
            let uu____1496 =
              let uu____1497 =
                let uu____1506 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1506  in
              [uu____1497]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1496
             in
          uu____1491 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1529 =
            let uu____1534 =
              let uu____1535 =
                let uu____1544 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1544  in
              let uu____1545 =
                let uu____1556 =
                  let uu____1565 =
                    let uu____1566 =
                      let uu____1571 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1571  in
                    embed uu____1566 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1565  in
                [uu____1556]  in
              uu____1535 :: uu____1545  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1534
             in
          uu____1529 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1601 =
            let uu____1606 =
              let uu____1607 =
                let uu____1616 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1616  in
              [uu____1607]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1606
             in
          uu____1601 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1634 =
            let uu____1639 =
              let uu____1640 =
                let uu____1649 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1649  in
              [uu____1640]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1639
             in
          uu____1634 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1668 =
            let uu____1673 =
              let uu____1674 =
                let uu____1683 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1683  in
              let uu____1684 =
                let uu____1695 =
                  let uu____1704 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1704  in
                [uu____1695]  in
              uu____1674 :: uu____1684  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1673
             in
          uu____1668 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1747 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1747 with
      | (hd1,args) ->
          let uu____1792 =
            let uu____1805 =
              let uu____1806 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1806.FStar_Syntax_Syntax.n  in
            (uu____1805, args)  in
          (match uu____1792 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1821)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1846 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1846
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _1853  -> FStar_Pervasives_Native.Some _1853)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1856)::(ps,uu____1858)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1893 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1893
                 (fun f1  ->
                    let uu____1899 =
                      let uu____1904 =
                        let uu____1909 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1909  in
                      unembed' w uu____1904 ps  in
                    FStar_Util.bind_opt uu____1899
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _1922  -> FStar_Pervasives_Native.Some _1922)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1927)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1952 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1952
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _1959  -> FStar_Pervasives_Native.Some _1959)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1962)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1987 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1987
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _1994  -> FStar_Pervasives_Native.Some _1994)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1997)::(t2,uu____1999)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____2034 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2034
                 (fun bv1  ->
                    let uu____2040 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____2040
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _2047  -> FStar_Pervasives_Native.Some _2047)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2048 ->
               (if w
                then
                  (let uu____2063 =
                     let uu____2069 =
                       let uu____2071 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2071
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2069)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2063)
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
    (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2098 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2098
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2113 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2113 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2136 =
            let uu____2141 =
              let uu____2142 =
                let uu____2151 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2151  in
              [uu____2142]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____2141
             in
          uu____2136 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2169 =
            let uu____2174 =
              let uu____2175 =
                let uu____2184 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2184  in
              [uu____2175]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2174
             in
          uu____2169 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2202 =
            let uu____2207 =
              let uu____2208 =
                let uu____2217 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2217  in
              [uu____2208]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2207
             in
          uu____2202 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2236 =
            let uu____2241 =
              let uu____2242 =
                let uu____2251 =
                  let uu____2252 = e_term_aq aq  in embed uu____2252 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2251  in
              let uu____2255 =
                let uu____2266 =
                  let uu____2275 =
                    let uu____2276 = e_argv_aq aq  in embed uu____2276 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2275  in
                [uu____2266]  in
              uu____2242 :: uu____2255  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2241
             in
          uu____2236 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2313 =
            let uu____2318 =
              let uu____2319 =
                let uu____2328 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2328  in
              let uu____2329 =
                let uu____2340 =
                  let uu____2349 =
                    let uu____2350 = e_term_aq aq  in embed uu____2350 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2349  in
                [uu____2340]  in
              uu____2319 :: uu____2329  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2318
             in
          uu____2313 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2379 =
            let uu____2384 =
              let uu____2385 =
                let uu____2394 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2394  in
              let uu____2395 =
                let uu____2406 =
                  let uu____2415 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2415  in
                [uu____2406]  in
              uu____2385 :: uu____2395  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2384
             in
          uu____2379 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2441 =
            let uu____2446 =
              let uu____2447 =
                let uu____2456 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2456  in
              [uu____2447]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2446
             in
          uu____2441 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2475 =
            let uu____2480 =
              let uu____2481 =
                let uu____2490 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2490  in
              let uu____2491 =
                let uu____2502 =
                  let uu____2511 =
                    let uu____2512 = e_term_aq aq  in embed uu____2512 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2511  in
                [uu____2502]  in
              uu____2481 :: uu____2491  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2480
             in
          uu____2475 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2540 =
            let uu____2545 =
              let uu____2546 =
                let uu____2555 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2555  in
              [uu____2546]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2545
             in
          uu____2540 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2574 =
            let uu____2579 =
              let uu____2580 =
                let uu____2589 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2589  in
              let uu____2590 =
                let uu____2601 =
                  let uu____2610 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2610  in
                [uu____2601]  in
              uu____2580 :: uu____2590  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2579
             in
          uu____2574 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2645 =
            let uu____2650 =
              let uu____2651 =
                let uu____2660 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2660  in
              let uu____2662 =
                let uu____2673 =
                  let uu____2682 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2682  in
                let uu____2683 =
                  let uu____2694 =
                    let uu____2703 =
                      let uu____2704 = e_term_aq aq  in
                      embed uu____2704 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2703  in
                  let uu____2707 =
                    let uu____2718 =
                      let uu____2727 =
                        let uu____2728 = e_term_aq aq  in
                        embed uu____2728 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2727  in
                    [uu____2718]  in
                  uu____2694 :: uu____2707  in
                uu____2673 :: uu____2683  in
              uu____2651 :: uu____2662  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2650
             in
          uu____2645 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2777 =
            let uu____2782 =
              let uu____2783 =
                let uu____2792 =
                  let uu____2793 = e_term_aq aq  in embed uu____2793 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2792  in
              let uu____2796 =
                let uu____2807 =
                  let uu____2816 =
                    let uu____2817 =
                      let uu____2826 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2826  in
                    embed uu____2817 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2816  in
                [uu____2807]  in
              uu____2783 :: uu____2796  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2782
             in
          uu____2777 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2874 =
            let uu____2879 =
              let uu____2880 =
                let uu____2889 =
                  let uu____2890 = e_term_aq aq  in embed uu____2890 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2889  in
              let uu____2893 =
                let uu____2904 =
                  let uu____2913 =
                    let uu____2914 = e_term_aq aq  in embed uu____2914 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2913  in
                let uu____2917 =
                  let uu____2928 =
                    let uu____2937 =
                      let uu____2938 =
                        let uu____2943 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2943  in
                      embed uu____2938 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2937  in
                  [uu____2928]  in
                uu____2904 :: uu____2917  in
              uu____2880 :: uu____2893  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2879
             in
          uu____2874 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2987 =
            let uu____2992 =
              let uu____2993 =
                let uu____3002 =
                  let uu____3003 = e_term_aq aq  in embed uu____3003 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3002  in
              let uu____3006 =
                let uu____3017 =
                  let uu____3026 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____3026  in
                let uu____3027 =
                  let uu____3038 =
                    let uu____3047 =
                      let uu____3048 =
                        let uu____3053 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3053  in
                      embed uu____3048 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3047  in
                  [uu____3038]  in
                uu____3017 :: uu____3027  in
              uu____2993 :: uu____3006  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2992
             in
          uu____2987 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___370_3090 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___370_3090.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___370_3090.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3108 = FStar_Syntax_Util.head_and_args t  in
      match uu____3108 with
      | (hd1,args) ->
          let uu____3153 =
            let uu____3166 =
              let uu____3167 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3167.FStar_Syntax_Syntax.n  in
            (uu____3166, args)  in
          (match uu____3153 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3182)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3207 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3207
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3214  -> FStar_Pervasives_Native.Some _3214)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3217)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3242 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3242
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3249  -> FStar_Pervasives_Native.Some _3249)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3252)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3277 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3277
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _3284  -> FStar_Pervasives_Native.Some _3284)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3287)::(r,uu____3289)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3324 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3324
                 (fun l1  ->
                    let uu____3330 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3330
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _3337  -> FStar_Pervasives_Native.Some _3337)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3340)::(t1,uu____3342)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3377 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3377
                 (fun b1  ->
                    let uu____3383 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3383
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3390  -> FStar_Pervasives_Native.Some _3390)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3393)::(t1,uu____3395)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3430 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3430
                 (fun b1  ->
                    let uu____3436 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3436
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _3443  -> FStar_Pervasives_Native.Some _3443)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3446)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3471 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3471
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _3478  -> FStar_Pervasives_Native.Some _3478)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3481)::(t1,uu____3483)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3518 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3518
                 (fun b1  ->
                    let uu____3524 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3524
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3531  -> FStar_Pervasives_Native.Some _3531)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3534)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3559 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3559
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _3566  -> FStar_Pervasives_Native.Some _3566)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3569)::(l,uu____3571)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3606 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3606
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _3615  -> FStar_Pervasives_Native.Some _3615)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3618)::(b,uu____3620)::(t1,uu____3622)::(t2,uu____3624)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3679 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3679
                 (fun r1  ->
                    let uu____3689 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3689
                      (fun b1  ->
                         let uu____3695 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3695
                           (fun t11  ->
                              let uu____3701 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3701
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _3708  ->
                                        FStar_Pervasives_Native.Some _3708)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3712)::(brs,uu____3714)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3749 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3749
                 (fun t2  ->
                    let uu____3755 =
                      let uu____3760 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3760 brs  in
                    FStar_Util.bind_opt uu____3755
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _3775  -> FStar_Pervasives_Native.Some _3775)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3780)::(t1,uu____3782)::(tacopt,uu____3784)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3829 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3829
                 (fun e1  ->
                    let uu____3835 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3835
                      (fun t2  ->
                         let uu____3841 =
                           let uu____3846 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3846 tacopt  in
                         FStar_Util.bind_opt uu____3841
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _3861  ->
                                   FStar_Pervasives_Native.Some _3861)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3866)::(c,uu____3868)::(tacopt,uu____3870)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3915 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3915
                 (fun e1  ->
                    let uu____3921 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3921
                      (fun c1  ->
                         let uu____3927 =
                           let uu____3932 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3932 tacopt  in
                         FStar_Util.bind_opt uu____3927
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _3947  ->
                                   FStar_Pervasives_Native.Some _3947)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _3967  -> FStar_Pervasives_Native.Some _3967)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____3968 ->
               (if w
                then
                  (let uu____3983 =
                     let uu____3989 =
                       let uu____3991 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3991
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3989)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3983)
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
    let uu____4020 =
      let uu____4025 =
        let uu____4026 =
          let uu____4035 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____4035  in
        let uu____4037 =
          let uu____4048 =
            let uu____4057 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4057  in
          let uu____4058 =
            let uu____4069 =
              let uu____4078 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4078  in
            [uu____4069]  in
          uu____4048 :: uu____4058  in
        uu____4026 :: uu____4037  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4025
       in
    uu____4020 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4129 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4129 with
    | (hd1,args) ->
        let uu____4174 =
          let uu____4187 =
            let uu____4188 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4188.FStar_Syntax_Syntax.n  in
          (uu____4187, args)  in
        (match uu____4174 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4203)::(idx,uu____4205)::(s,uu____4207)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4252 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4252
               (fun nm1  ->
                  let uu____4262 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4262
                    (fun idx1  ->
                       let uu____4268 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4268
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _4275  ->
                                 FStar_Pervasives_Native.Some _4275)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4276 ->
             (if w
              then
                (let uu____4291 =
                   let uu____4297 =
                     let uu____4299 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4299
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4297)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4291)
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
        let uu____4325 =
          let uu____4330 =
            let uu____4331 =
              let uu____4340 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4340  in
            let uu____4341 =
              let uu____4352 =
                let uu____4361 =
                  let uu____4362 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4362 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4361  in
              [uu____4352]  in
            uu____4331 :: uu____4341  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4330
           in
        uu____4325 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4398 =
          let uu____4403 =
            let uu____4404 =
              let uu____4413 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4413  in
            let uu____4414 =
              let uu____4425 =
                let uu____4434 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4434  in
              [uu____4425]  in
            uu____4404 :: uu____4414  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4403
           in
        uu____4398 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___591_4459 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___591_4459.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___591_4459.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4478 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4478 with
    | (hd1,args) ->
        let uu____4523 =
          let uu____4536 =
            let uu____4537 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4537.FStar_Syntax_Syntax.n  in
          (uu____4536, args)  in
        (match uu____4523 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4552)::(md,uu____4554)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4589 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4589
               (fun t3  ->
                  let uu____4595 =
                    let uu____4600 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4600 md  in
                  FStar_Util.bind_opt uu____4595
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _4615  -> FStar_Pervasives_Native.Some _4615)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4620)::(post,uu____4622)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4657 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4657
               (fun pre1  ->
                  let uu____4663 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4663
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _4670  -> FStar_Pervasives_Native.Some _4670)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _4688  -> FStar_Pervasives_Native.Some _4688)
               FStar_Reflection_Data.C_Unknown
         | uu____4689 ->
             (if w
              then
                (let uu____4704 =
                   let uu____4710 =
                     let uu____4712 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4712
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4710)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4704)
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
    let uu___638_4737 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___638_4737.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___638_4737.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4758 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4758 with
    | (hd1,args) ->
        let uu____4803 =
          let uu____4818 =
            let uu____4819 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4819.FStar_Syntax_Syntax.n  in
          (uu____4818, args)  in
        (match uu____4803 with
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
         | uu____4891 ->
             (if w
              then
                (let uu____4908 =
                   let uu____4914 =
                     let uu____4916 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4916
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4914)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4908)
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
    let uu____4953 =
      let uu____4954 = FStar_Syntax_Subst.compress t  in
      uu____4954.FStar_Syntax_Syntax.n  in
    match uu____4953 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____4960;
          FStar_Syntax_Syntax.rng = uu____4961;_}
        ->
        let uu____4964 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4964
    | uu____4965 ->
        (if w
         then
           (let uu____4968 =
              let uu____4974 =
                let uu____4976 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4976
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4974)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4968)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____5016 uu____5017 =
    let uu____5019 =
      let uu____5025 = FStar_Ident.range_of_id i  in
      let uu____5026 = FStar_Ident.text_of_id i  in (uu____5025, uu____5026)
       in
    embed repr rng uu____5019  in
  let unembed_ident t w uu____5053 =
    let uu____5058 = unembed' w repr t  in
    match uu____5058 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5082 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5082
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5089 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5089
  
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
        let uu____5128 =
          let uu____5133 =
            let uu____5134 =
              let uu____5143 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5143  in
            let uu____5145 =
              let uu____5156 =
                let uu____5165 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5165  in
              let uu____5166 =
                let uu____5177 =
                  let uu____5186 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5186  in
                let uu____5189 =
                  let uu____5200 =
                    let uu____5209 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5209  in
                  let uu____5210 =
                    let uu____5221 =
                      let uu____5230 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5230  in
                    [uu____5221]  in
                  uu____5200 :: uu____5210  in
                uu____5177 :: uu____5189  in
              uu____5156 :: uu____5166  in
            uu____5134 :: uu____5145  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5133
           in
        uu____5128 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5281 =
          let uu____5286 =
            let uu____5287 =
              let uu____5296 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5296  in
            let uu____5300 =
              let uu____5311 =
                let uu____5320 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5320  in
              [uu____5311]  in
            uu____5287 :: uu____5300  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5286
           in
        uu____5281 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5362 =
          let uu____5367 =
            let uu____5368 =
              let uu____5377 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5377  in
            let uu____5381 =
              let uu____5392 =
                let uu____5401 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5401  in
              let uu____5404 =
                let uu____5415 =
                  let uu____5424 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5424  in
                let uu____5425 =
                  let uu____5436 =
                    let uu____5445 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5445  in
                  let uu____5446 =
                    let uu____5457 =
                      let uu____5466 =
                        let uu____5467 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5467 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5466  in
                    [uu____5457]  in
                  uu____5436 :: uu____5446  in
                uu____5415 :: uu____5425  in
              uu____5392 :: uu____5404  in
            uu____5368 :: uu____5381  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5367
           in
        uu____5362 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___714_5531 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___714_5531.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___714_5531.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5550 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5550 with
    | (hd1,args) ->
        let uu____5595 =
          let uu____5608 =
            let uu____5609 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5609.FStar_Syntax_Syntax.n  in
          (uu____5608, args)  in
        (match uu____5595 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5624)::(us,uu____5626)::(bs,uu____5628)::(t2,uu____5630)::
            (dcs,uu____5632)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5697 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5697
               (fun nm1  ->
                  let uu____5715 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5715
                    (fun us1  ->
                       let uu____5729 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5729
                         (fun bs1  ->
                            let uu____5735 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5735
                              (fun t3  ->
                                 let uu____5741 =
                                   let uu____5749 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5749 dcs  in
                                 FStar_Util.bind_opt uu____5741
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _5779  ->
                                           FStar_Pervasives_Native.Some _5779)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5788)::(fvar1,uu____5790)::(univs1,uu____5792)::
            (ty,uu____5794)::(t2,uu____5796)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5861 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5861
               (fun r1  ->
                  let uu____5871 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5871
                    (fun fvar2  ->
                       let uu____5877 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5877
                         (fun univs2  ->
                            let uu____5891 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____5891
                              (fun ty1  ->
                                 let uu____5897 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____5897
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _5904  ->
                                           FStar_Pervasives_Native.Some _5904)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____5923 ->
             (if w
              then
                (let uu____5938 =
                   let uu____5944 =
                     let uu____5946 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5946
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5944)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5938)
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
          let uu____5972 =
            let uu____5977 =
              let uu____5978 =
                let uu____5987 =
                  let uu____5988 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5988  in
                FStar_Syntax_Syntax.as_arg uu____5987  in
              [uu____5978]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5977
             in
          uu____5972 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6008 =
            let uu____6013 =
              let uu____6014 =
                let uu____6023 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6023  in
              let uu____6024 =
                let uu____6035 =
                  let uu____6044 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6044  in
                [uu____6035]  in
              uu____6014 :: uu____6024  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6013
             in
          uu____6008 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___789_6069 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___789_6069.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___789_6069.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6090 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6090 with
    | (hd1,args) ->
        let uu____6135 =
          let uu____6148 =
            let uu____6149 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6149.FStar_Syntax_Syntax.n  in
          (uu____6148, args)  in
        (match uu____6135 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6179)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6204 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6204
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _6211  -> FStar_Pervasives_Native.Some _6211)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6214)::(e2,uu____6216)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6251 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6251
               (fun e11  ->
                  let uu____6257 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6257
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _6264  -> FStar_Pervasives_Native.Some _6264)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6265 ->
             (if w
              then
                (let uu____6280 =
                   let uu____6286 =
                     let uu____6288 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6288
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6286)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6280)
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
    let uu____6312 =
      let uu____6317 =
        let uu____6318 =
          let uu____6327 =
            let uu____6328 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____6328  in
          FStar_Syntax_Syntax.as_arg uu____6327  in
        [uu____6318]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____6317
       in
    uu____6312 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6352 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____6352 with
    | (bv,aq) ->
        let uu____6359 =
          let uu____6364 =
            let uu____6365 =
              let uu____6374 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____6374  in
            let uu____6375 =
              let uu____6386 =
                let uu____6395 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____6395  in
              [uu____6386]  in
            uu____6365 :: uu____6375  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____6364
           in
        uu____6359 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6427 =
      let uu____6432 =
        let uu____6433 =
          let uu____6442 =
            let uu____6443 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____6450 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____6443 i.FStar_Syntax_Syntax.rng uu____6450  in
          FStar_Syntax_Syntax.as_arg uu____6442  in
        [uu____6433]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____6432
       in
    uu____6427 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6480 =
      let uu____6485 =
        let uu____6486 =
          let uu____6495 =
            let uu____6496 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____6496  in
          FStar_Syntax_Syntax.as_arg uu____6495  in
        [uu____6486]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____6485
       in
    uu____6480 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6526 =
      let uu____6531 =
        let uu____6532 =
          let uu____6541 =
            let uu____6542 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____6542  in
          FStar_Syntax_Syntax.as_arg uu____6541  in
        [uu____6532]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6531
       in
    uu____6526 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  