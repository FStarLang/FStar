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
          let uu____1539 =
            let uu____1544 =
              let uu____1545 =
                let uu____1554 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1554  in
              let uu____1555 =
                let uu____1566 =
                  let uu____1575 =
                    let uu____1576 =
                      let uu____1586 =
                        let uu____1594 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_tuple2 uu____1594
                          FStar_Syntax_Embeddings.e_bool
                         in
                      FStar_Syntax_Embeddings.e_list uu____1586  in
                    embed uu____1576 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1575  in
                [uu____1566]  in
              uu____1545 :: uu____1555  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1544
             in
          uu____1539 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1635 =
            let uu____1640 =
              let uu____1641 =
                let uu____1650 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1650  in
              [uu____1641]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1640
             in
          uu____1635 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1668 =
            let uu____1673 =
              let uu____1674 =
                let uu____1683 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1683  in
              [uu____1674]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1673
             in
          uu____1668 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1702 =
            let uu____1707 =
              let uu____1708 =
                let uu____1717 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1717  in
              let uu____1718 =
                let uu____1729 =
                  let uu____1738 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1738  in
                [uu____1729]  in
              uu____1708 :: uu____1718  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1707
             in
          uu____1702 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1781 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1781 with
      | (hd1,args) ->
          let uu____1826 =
            let uu____1839 =
              let uu____1840 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1840.FStar_Syntax_Syntax.n  in
            (uu____1839, args)  in
          (match uu____1826 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1855)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1880 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1880
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _1887  -> FStar_Pervasives_Native.Some _1887)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1890)::(ps,uu____1892)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1927 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1927
                 (fun f1  ->
                    let uu____1933 =
                      let uu____1943 =
                        let uu____1953 =
                          let uu____1961 = e_pattern' ()  in
                          FStar_Syntax_Embeddings.e_tuple2 uu____1961
                            FStar_Syntax_Embeddings.e_bool
                           in
                        FStar_Syntax_Embeddings.e_list uu____1953  in
                      unembed' w uu____1943 ps  in
                    FStar_Util.bind_opt uu____1933
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _1995  -> FStar_Pervasives_Native.Some _1995)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2005)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____2030 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2030
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2037  -> FStar_Pervasives_Native.Some _2037)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2040)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____2065 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2065
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2072  -> FStar_Pervasives_Native.Some _2072)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____2075)::(t2,uu____2077)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____2112 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2112
                 (fun bv1  ->
                    let uu____2118 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____2118
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _2125  -> FStar_Pervasives_Native.Some _2125)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2126 ->
               (if w
                then
                  (let uu____2141 =
                     let uu____2147 =
                       let uu____2149 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2149
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2147)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2141)
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
    let uu____2176 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2176
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2191 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2191 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2214 =
            let uu____2219 =
              let uu____2220 =
                let uu____2229 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2229  in
              [uu____2220]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____2219
             in
          uu____2214 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2247 =
            let uu____2252 =
              let uu____2253 =
                let uu____2262 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2262  in
              [uu____2253]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2252
             in
          uu____2247 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2280 =
            let uu____2285 =
              let uu____2286 =
                let uu____2295 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2295  in
              [uu____2286]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2285
             in
          uu____2280 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2314 =
            let uu____2319 =
              let uu____2320 =
                let uu____2329 =
                  let uu____2330 = e_term_aq aq  in embed uu____2330 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2329  in
              let uu____2333 =
                let uu____2344 =
                  let uu____2353 =
                    let uu____2354 = e_argv_aq aq  in embed uu____2354 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2353  in
                [uu____2344]  in
              uu____2320 :: uu____2333  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2319
             in
          uu____2314 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2391 =
            let uu____2396 =
              let uu____2397 =
                let uu____2406 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2406  in
              let uu____2407 =
                let uu____2418 =
                  let uu____2427 =
                    let uu____2428 = e_term_aq aq  in embed uu____2428 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2427  in
                [uu____2418]  in
              uu____2397 :: uu____2407  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2396
             in
          uu____2391 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2457 =
            let uu____2462 =
              let uu____2463 =
                let uu____2472 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2472  in
              let uu____2473 =
                let uu____2484 =
                  let uu____2493 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2493  in
                [uu____2484]  in
              uu____2463 :: uu____2473  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2462
             in
          uu____2457 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2519 =
            let uu____2524 =
              let uu____2525 =
                let uu____2534 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2534  in
              [uu____2525]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2524
             in
          uu____2519 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2553 =
            let uu____2558 =
              let uu____2559 =
                let uu____2568 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2568  in
              let uu____2569 =
                let uu____2580 =
                  let uu____2589 =
                    let uu____2590 = e_term_aq aq  in embed uu____2590 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2589  in
                [uu____2580]  in
              uu____2559 :: uu____2569  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2558
             in
          uu____2553 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2618 =
            let uu____2623 =
              let uu____2624 =
                let uu____2633 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2633  in
              [uu____2624]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2623
             in
          uu____2618 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2652 =
            let uu____2657 =
              let uu____2658 =
                let uu____2667 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2667  in
              let uu____2668 =
                let uu____2679 =
                  let uu____2688 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2688  in
                [uu____2679]  in
              uu____2658 :: uu____2668  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2657
             in
          uu____2652 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2723 =
            let uu____2728 =
              let uu____2729 =
                let uu____2738 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2738  in
              let uu____2740 =
                let uu____2751 =
                  let uu____2760 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2760  in
                let uu____2761 =
                  let uu____2772 =
                    let uu____2781 =
                      let uu____2782 = e_term_aq aq  in
                      embed uu____2782 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2781  in
                  let uu____2785 =
                    let uu____2796 =
                      let uu____2805 =
                        let uu____2806 = e_term_aq aq  in
                        embed uu____2806 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2805  in
                    [uu____2796]  in
                  uu____2772 :: uu____2785  in
                uu____2751 :: uu____2761  in
              uu____2729 :: uu____2740  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2728
             in
          uu____2723 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2855 =
            let uu____2860 =
              let uu____2861 =
                let uu____2870 =
                  let uu____2871 = e_term_aq aq  in embed uu____2871 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2870  in
              let uu____2874 =
                let uu____2885 =
                  let uu____2894 =
                    let uu____2895 =
                      let uu____2904 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2904  in
                    embed uu____2895 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2894  in
                [uu____2885]  in
              uu____2861 :: uu____2874  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2860
             in
          uu____2855 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2952 =
            let uu____2957 =
              let uu____2958 =
                let uu____2967 =
                  let uu____2968 = e_term_aq aq  in embed uu____2968 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2967  in
              let uu____2971 =
                let uu____2982 =
                  let uu____2991 =
                    let uu____2992 = e_term_aq aq  in embed uu____2992 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2991  in
                let uu____2995 =
                  let uu____3006 =
                    let uu____3015 =
                      let uu____3016 =
                        let uu____3021 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3021  in
                      embed uu____3016 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3015  in
                  [uu____3006]  in
                uu____2982 :: uu____2995  in
              uu____2958 :: uu____2971  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2957
             in
          uu____2952 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____3065 =
            let uu____3070 =
              let uu____3071 =
                let uu____3080 =
                  let uu____3081 = e_term_aq aq  in embed uu____3081 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3080  in
              let uu____3084 =
                let uu____3095 =
                  let uu____3104 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____3104  in
                let uu____3105 =
                  let uu____3116 =
                    let uu____3125 =
                      let uu____3126 =
                        let uu____3131 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3131  in
                      embed uu____3126 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3125  in
                  [uu____3116]  in
                uu____3095 :: uu____3105  in
              uu____3071 :: uu____3084  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____3070
             in
          uu____3065 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___370_3168 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___370_3168.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___370_3168.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3186 = FStar_Syntax_Util.head_and_args t  in
      match uu____3186 with
      | (hd1,args) ->
          let uu____3231 =
            let uu____3244 =
              let uu____3245 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3245.FStar_Syntax_Syntax.n  in
            (uu____3244, args)  in
          (match uu____3231 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3260)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3285 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3285
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3292  -> FStar_Pervasives_Native.Some _3292)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3295)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3320 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3320
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3327  -> FStar_Pervasives_Native.Some _3327)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3330)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3355 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3355
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _3362  -> FStar_Pervasives_Native.Some _3362)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3365)::(r,uu____3367)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3402 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3402
                 (fun l1  ->
                    let uu____3408 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3408
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _3415  -> FStar_Pervasives_Native.Some _3415)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3418)::(t1,uu____3420)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3455 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3455
                 (fun b1  ->
                    let uu____3461 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3461
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3468  -> FStar_Pervasives_Native.Some _3468)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3471)::(t1,uu____3473)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3508 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3508
                 (fun b1  ->
                    let uu____3514 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3514
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _3521  -> FStar_Pervasives_Native.Some _3521)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3524)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3549 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3549
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _3556  -> FStar_Pervasives_Native.Some _3556)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3559)::(t1,uu____3561)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3596 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3596
                 (fun b1  ->
                    let uu____3602 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3602
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3609  -> FStar_Pervasives_Native.Some _3609)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3612)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3637 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3637
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _3644  -> FStar_Pervasives_Native.Some _3644)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3647)::(l,uu____3649)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3684 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3684
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _3693  -> FStar_Pervasives_Native.Some _3693)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3696)::(b,uu____3698)::(t1,uu____3700)::(t2,uu____3702)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3757 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3757
                 (fun r1  ->
                    let uu____3767 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3767
                      (fun b1  ->
                         let uu____3773 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3773
                           (fun t11  ->
                              let uu____3779 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3779
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _3786  ->
                                        FStar_Pervasives_Native.Some _3786)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3790)::(brs,uu____3792)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3827 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3827
                 (fun t2  ->
                    let uu____3833 =
                      let uu____3838 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3838 brs  in
                    FStar_Util.bind_opt uu____3833
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _3853  -> FStar_Pervasives_Native.Some _3853)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3858)::(t1,uu____3860)::(tacopt,uu____3862)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3907 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3907
                 (fun e1  ->
                    let uu____3913 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3913
                      (fun t2  ->
                         let uu____3919 =
                           let uu____3924 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3924 tacopt  in
                         FStar_Util.bind_opt uu____3919
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _3939  ->
                                   FStar_Pervasives_Native.Some _3939)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3944)::(c,uu____3946)::(tacopt,uu____3948)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3993 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3993
                 (fun e1  ->
                    let uu____3999 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3999
                      (fun c1  ->
                         let uu____4005 =
                           let uu____4010 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4010 tacopt  in
                         FStar_Util.bind_opt uu____4005
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4025  ->
                                   FStar_Pervasives_Native.Some _4025)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _4045  -> FStar_Pervasives_Native.Some _4045)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____4046 ->
               (if w
                then
                  (let uu____4061 =
                     let uu____4067 =
                       let uu____4069 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4069
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4067)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____4061)
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
    let uu____4098 =
      let uu____4103 =
        let uu____4104 =
          let uu____4113 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____4113  in
        let uu____4115 =
          let uu____4126 =
            let uu____4135 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4135  in
          let uu____4136 =
            let uu____4147 =
              let uu____4156 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4156  in
            [uu____4147]  in
          uu____4126 :: uu____4136  in
        uu____4104 :: uu____4115  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4103
       in
    uu____4098 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4207 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4207 with
    | (hd1,args) ->
        let uu____4252 =
          let uu____4265 =
            let uu____4266 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4266.FStar_Syntax_Syntax.n  in
          (uu____4265, args)  in
        (match uu____4252 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4281)::(idx,uu____4283)::(s,uu____4285)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4330 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4330
               (fun nm1  ->
                  let uu____4340 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4340
                    (fun idx1  ->
                       let uu____4346 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4346
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _4353  ->
                                 FStar_Pervasives_Native.Some _4353)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4354 ->
             (if w
              then
                (let uu____4369 =
                   let uu____4375 =
                     let uu____4377 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4377
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4375)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4369)
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
        let uu____4403 =
          let uu____4408 =
            let uu____4409 =
              let uu____4418 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4418  in
            let uu____4419 =
              let uu____4430 =
                let uu____4439 =
                  let uu____4440 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4440 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4439  in
              [uu____4430]  in
            uu____4409 :: uu____4419  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4408
           in
        uu____4403 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4476 =
          let uu____4481 =
            let uu____4482 =
              let uu____4491 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4491  in
            let uu____4492 =
              let uu____4503 =
                let uu____4512 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4512  in
              [uu____4503]  in
            uu____4482 :: uu____4492  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4481
           in
        uu____4476 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___591_4537 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___591_4537.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___591_4537.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4556 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4556 with
    | (hd1,args) ->
        let uu____4601 =
          let uu____4614 =
            let uu____4615 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4615.FStar_Syntax_Syntax.n  in
          (uu____4614, args)  in
        (match uu____4601 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4630)::(md,uu____4632)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4667 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4667
               (fun t3  ->
                  let uu____4673 =
                    let uu____4678 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4678 md  in
                  FStar_Util.bind_opt uu____4673
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _4693  -> FStar_Pervasives_Native.Some _4693)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4698)::(post,uu____4700)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4735 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4735
               (fun pre1  ->
                  let uu____4741 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4741
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _4748  -> FStar_Pervasives_Native.Some _4748)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _4766  -> FStar_Pervasives_Native.Some _4766)
               FStar_Reflection_Data.C_Unknown
         | uu____4767 ->
             (if w
              then
                (let uu____4782 =
                   let uu____4788 =
                     let uu____4790 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4790
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4788)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4782)
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
    let uu___638_4815 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___638_4815.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___638_4815.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4836 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4836 with
    | (hd1,args) ->
        let uu____4881 =
          let uu____4896 =
            let uu____4897 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4897.FStar_Syntax_Syntax.n  in
          (uu____4896, args)  in
        (match uu____4881 with
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
         | uu____4969 ->
             (if w
              then
                (let uu____4986 =
                   let uu____4992 =
                     let uu____4994 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4994
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4992)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4986)
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
    let uu____5031 =
      let uu____5032 = FStar_Syntax_Subst.compress t  in
      uu____5032.FStar_Syntax_Syntax.n  in
    match uu____5031 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5038;
          FStar_Syntax_Syntax.rng = uu____5039;_}
        ->
        let uu____5042 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5042
    | uu____5043 ->
        (if w
         then
           (let uu____5046 =
              let uu____5052 =
                let uu____5054 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5054
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5052)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5046)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____5094 uu____5095 =
    let uu____5097 =
      let uu____5103 = FStar_Ident.range_of_id i  in
      let uu____5104 = FStar_Ident.text_of_id i  in (uu____5103, uu____5104)
       in
    embed repr rng uu____5097  in
  let unembed_ident t w uu____5131 =
    let uu____5136 = unembed' w repr t  in
    match uu____5136 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5160 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5160
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5167 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5167
  
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
        let uu____5206 =
          let uu____5211 =
            let uu____5212 =
              let uu____5221 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5221  in
            let uu____5223 =
              let uu____5234 =
                let uu____5243 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5243  in
              let uu____5244 =
                let uu____5255 =
                  let uu____5264 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5264  in
                let uu____5267 =
                  let uu____5278 =
                    let uu____5287 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5287  in
                  let uu____5288 =
                    let uu____5299 =
                      let uu____5308 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5308  in
                    [uu____5299]  in
                  uu____5278 :: uu____5288  in
                uu____5255 :: uu____5267  in
              uu____5234 :: uu____5244  in
            uu____5212 :: uu____5223  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5211
           in
        uu____5206 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5359 =
          let uu____5364 =
            let uu____5365 =
              let uu____5374 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5374  in
            let uu____5378 =
              let uu____5389 =
                let uu____5398 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5398  in
              [uu____5389]  in
            uu____5365 :: uu____5378  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5364
           in
        uu____5359 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5440 =
          let uu____5445 =
            let uu____5446 =
              let uu____5455 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5455  in
            let uu____5459 =
              let uu____5470 =
                let uu____5479 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5479  in
              let uu____5482 =
                let uu____5493 =
                  let uu____5502 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5502  in
                let uu____5503 =
                  let uu____5514 =
                    let uu____5523 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5523  in
                  let uu____5524 =
                    let uu____5535 =
                      let uu____5544 =
                        let uu____5545 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5545 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5544  in
                    [uu____5535]  in
                  uu____5514 :: uu____5524  in
                uu____5493 :: uu____5503  in
              uu____5470 :: uu____5482  in
            uu____5446 :: uu____5459  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5445
           in
        uu____5440 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___714_5609 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___714_5609.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___714_5609.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5628 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5628 with
    | (hd1,args) ->
        let uu____5673 =
          let uu____5686 =
            let uu____5687 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5687.FStar_Syntax_Syntax.n  in
          (uu____5686, args)  in
        (match uu____5673 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5702)::(us,uu____5704)::(bs,uu____5706)::(t2,uu____5708)::
            (dcs,uu____5710)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5775 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5775
               (fun nm1  ->
                  let uu____5793 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5793
                    (fun us1  ->
                       let uu____5807 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5807
                         (fun bs1  ->
                            let uu____5813 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5813
                              (fun t3  ->
                                 let uu____5819 =
                                   let uu____5827 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5827 dcs  in
                                 FStar_Util.bind_opt uu____5819
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _5857  ->
                                           FStar_Pervasives_Native.Some _5857)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5866)::(fvar1,uu____5868)::(univs1,uu____5870)::
            (ty,uu____5872)::(t2,uu____5874)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5939 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5939
               (fun r1  ->
                  let uu____5949 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5949
                    (fun fvar2  ->
                       let uu____5955 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5955
                         (fun univs2  ->
                            let uu____5969 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____5969
                              (fun ty1  ->
                                 let uu____5975 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____5975
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _5982  ->
                                           FStar_Pervasives_Native.Some _5982)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6001 ->
             (if w
              then
                (let uu____6016 =
                   let uu____6022 =
                     let uu____6024 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6024
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6022)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6016)
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
          let uu____6050 =
            let uu____6055 =
              let uu____6056 =
                let uu____6065 =
                  let uu____6066 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6066  in
                FStar_Syntax_Syntax.as_arg uu____6065  in
              [uu____6056]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6055
             in
          uu____6050 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6086 =
            let uu____6091 =
              let uu____6092 =
                let uu____6101 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6101  in
              let uu____6102 =
                let uu____6113 =
                  let uu____6122 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6122  in
                [uu____6113]  in
              uu____6092 :: uu____6102  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6091
             in
          uu____6086 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___789_6147 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___789_6147.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___789_6147.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6168 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6168 with
    | (hd1,args) ->
        let uu____6213 =
          let uu____6226 =
            let uu____6227 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6227.FStar_Syntax_Syntax.n  in
          (uu____6226, args)  in
        (match uu____6213 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6257)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6282 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6282
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _6289  -> FStar_Pervasives_Native.Some _6289)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6292)::(e2,uu____6294)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6329 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6329
               (fun e11  ->
                  let uu____6335 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6335
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _6342  -> FStar_Pervasives_Native.Some _6342)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6343 ->
             (if w
              then
                (let uu____6358 =
                   let uu____6364 =
                     let uu____6366 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6366
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6364)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6358)
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
let (e_lid : FStar_Ident.lid FStar_Syntax_Embeddings.embedding) =
  let embed1 rng lid =
    let uu____6397 = FStar_Ident.path_of_lid lid  in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____6397  in
  let unembed1 w t =
    let uu____6425 = unembed' w FStar_Syntax_Embeddings.e_string_list t  in
    FStar_Util.map_opt uu____6425
      (fun p  -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos)
     in
  let uu____6442 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x  -> fun r  -> fun uu____6449  -> fun uu____6450  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____6457  -> unembed1 w x) uu____6442
    FStar_Ident.string_of_lid FStar_Syntax_Syntax.ET_abstract
  
let (e_qualifier :
  FStar_Syntax_Syntax.qualifier FStar_Syntax_Embeddings.embedding) =
  let embed1 rng q =
    let r =
      match q with
      | FStar_Syntax_Syntax.Assumption  ->
          FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.New  ->
          FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Private  ->
          FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
          FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Visible_default  ->
          FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Irreducible  ->
          FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Abstract  ->
          FStar_Reflection_Data.ref_qual_Abstract.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Inline_for_extraction  ->
          FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.NoExtract  ->
          FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Noeq  ->
          FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Unopteq  ->
          FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.TotalEffect  ->
          FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Logic  ->
          FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Reifiable  ->
          FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.ExceptionConstructor  ->
          FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.HasMaskedEffect  ->
          FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Effect  ->
          FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.OnlyName  ->
          FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.t
      | FStar_Syntax_Syntax.Reflectable l ->
          let uu____6480 =
            let uu____6485 =
              let uu____6486 =
                let uu____6495 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6495  in
              [uu____6486]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
              uu____6485
             in
          uu____6480 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Discriminator l ->
          let uu____6513 =
            let uu____6518 =
              let uu____6519 =
                let uu____6528 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6528  in
              [uu____6519]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
              uu____6518
             in
          uu____6513 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Action l ->
          let uu____6546 =
            let uu____6551 =
              let uu____6552 =
                let uu____6561 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6561  in
              [uu____6552]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
              uu____6551
             in
          uu____6546 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Projector (l,i) ->
          let uu____6580 =
            let uu____6585 =
              let uu____6586 =
                let uu____6595 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6595  in
              let uu____6596 =
                let uu____6607 =
                  let uu____6616 = embed e_ident rng i  in
                  FStar_Syntax_Syntax.as_arg uu____6616  in
                [uu____6607]  in
              uu____6586 :: uu____6596  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
              uu____6585
             in
          uu____6580 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.RecordType (ids1,ids2) ->
          let uu____6651 =
            let uu____6656 =
              let uu____6657 =
                let uu____6666 =
                  let uu____6667 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6667 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6666  in
              let uu____6674 =
                let uu____6685 =
                  let uu____6694 =
                    let uu____6695 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6695 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6694  in
                [uu____6685]  in
              uu____6657 :: uu____6674  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
              uu____6656
             in
          uu____6651 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.RecordConstructor (ids1,ids2) ->
          let uu____6736 =
            let uu____6741 =
              let uu____6742 =
                let uu____6751 =
                  let uu____6752 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6752 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6751  in
              let uu____6759 =
                let uu____6770 =
                  let uu____6779 =
                    let uu____6780 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6780 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6779  in
                [uu____6770]  in
              uu____6742 :: uu____6759  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
              uu____6741
             in
          uu____6736 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___879_6811 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___879_6811.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___879_6811.FStar_Syntax_Syntax.vars)
    }  in
  let unembed1 w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6832 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6832 with
    | (hd1,args) ->
        let uu____6877 =
          let uu____6890 =
            let uu____6891 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6891.FStar_Syntax_Syntax.n  in
          (uu____6890, args)  in
        (match uu____6877 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Assumption
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.New
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Private
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Visible_default
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Irreducible
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Abstract.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Abstract
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Syntax_Syntax.Inline_for_extraction
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.NoExtract
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Noeq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Unopteq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.TotalEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Logic
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Reifiable
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Syntax_Syntax.ExceptionConstructor
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.HasMaskedEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Effect
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.OnlyName
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7176)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7201 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7201
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7208  -> FStar_Pervasives_Native.Some _7208)
                    (FStar_Syntax_Syntax.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7211)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7236 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7236
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7243  -> FStar_Pervasives_Native.Some _7243)
                    (FStar_Syntax_Syntax.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7246)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7271 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7271
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7278  -> FStar_Pervasives_Native.Some _7278)
                    (FStar_Syntax_Syntax.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7281)::(i,uu____7283)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7318 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7318
               (fun l1  ->
                  let uu____7324 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7324
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun _7331  -> FStar_Pervasives_Native.Some _7331)
                         (FStar_Syntax_Syntax.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7334)::(ids2,uu____7336)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7371 =
               let uu____7376 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7376 ids1  in
             FStar_Util.bind_opt uu____7371
               (fun ids11  ->
                  let uu____7390 =
                    let uu____7395 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7395 ids2  in
                  FStar_Util.bind_opt uu____7390
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7410  -> FStar_Pervasives_Native.Some _7410)
                         (FStar_Syntax_Syntax.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7417)::(ids2,uu____7419)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____7454 =
               let uu____7459 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7459 ids1  in
             FStar_Util.bind_opt uu____7454
               (fun ids11  ->
                  let uu____7473 =
                    let uu____7478 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7478 ids2  in
                  FStar_Util.bind_opt uu____7473
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7493  -> FStar_Pervasives_Native.Some _7493)
                         (FStar_Syntax_Syntax.RecordConstructor
                            (ids11, ids21))))
         | uu____7498 ->
             (if w
              then
                (let uu____7513 =
                   let uu____7519 =
                     let uu____7521 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____7521
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____7519)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7513)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed1 unembed1 FStar_Reflection_Data.fstar_refl_qualifier 
let (e_qualifiers :
  FStar_Syntax_Syntax.qualifier Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_qualifier 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7539 =
      let uu____7544 =
        let uu____7545 =
          let uu____7554 =
            let uu____7555 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____7555  in
          FStar_Syntax_Syntax.as_arg uu____7554  in
        [uu____7545]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____7544
       in
    uu____7539 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7579 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____7579 with
    | (bv,aq) ->
        let uu____7586 =
          let uu____7591 =
            let uu____7592 =
              let uu____7601 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____7601  in
            let uu____7602 =
              let uu____7613 =
                let uu____7622 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____7622  in
              [uu____7613]  in
            uu____7592 :: uu____7602  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____7591
           in
        uu____7586 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7654 =
      let uu____7659 =
        let uu____7660 =
          let uu____7669 =
            let uu____7670 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____7677 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____7670 i.FStar_Syntax_Syntax.rng uu____7677  in
          FStar_Syntax_Syntax.as_arg uu____7669  in
        [uu____7660]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____7659
       in
    uu____7654 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7707 =
      let uu____7712 =
        let uu____7713 =
          let uu____7722 =
            let uu____7723 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____7723  in
          FStar_Syntax_Syntax.as_arg uu____7722  in
        [uu____7713]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____7712
       in
    uu____7707 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7753 =
      let uu____7758 =
        let uu____7759 =
          let uu____7768 =
            let uu____7769 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____7769  in
          FStar_Syntax_Syntax.as_arg uu____7768  in
        [uu____7759]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____7758
       in
    uu____7753 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  