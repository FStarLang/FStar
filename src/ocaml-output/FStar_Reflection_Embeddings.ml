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
let (e_optionstate :
  FStar_Options.optionstate FStar_Syntax_Embeddings.embedding) =
  let embed_optionstate rng b =
    FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_optionstate
      FStar_Syntax_Syntax.Lazy_optionstate (FStar_Pervasives_Native.Some rng)
     in
  let unembed_optionstate w t =
    let uu____299 =
      let uu____300 = FStar_Syntax_Subst.compress t  in
      uu____300.FStar_Syntax_Syntax.n  in
    match uu____299 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_optionstate ;
          FStar_Syntax_Syntax.ltyp = uu____306;
          FStar_Syntax_Syntax.rng = uu____307;_}
        ->
        let uu____310 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____310
    | uu____311 ->
        (if w
         then
           (let uu____314 =
              let uu____320 =
                let uu____322 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded optionstate: %s"
                  uu____322
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____320)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____314)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_optionstate unembed_optionstate
    FStar_Reflection_Data.fstar_refl_optionstate
  
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
          let uu____374 = f x  in
          FStar_Util.bind_opt uu____374
            (fun x1  ->
               let uu____382 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____382
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
        let uu____451 =
          mapM_opt
            (fun uu____464  ->
               match uu____464 with
               | (bv,e) ->
                   let uu____473 = unembed_term w e  in
                   FStar_Util.bind_opt uu____473
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____451
          (fun s  ->
             let uu____487 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____487)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____489 =
        let uu____490 = FStar_Syntax_Subst.compress t1  in
        uu____490.FStar_Syntax_Syntax.n  in
      match uu____489 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____501 ->
          (if w
           then
             (let uu____504 =
                let uu____510 =
                  let uu____512 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____512  in
                (FStar_Errors.Warning_NotEmbedded, uu____510)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____504)
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
          let uu____547 =
            let uu____552 =
              let uu____553 =
                let uu____562 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____562  in
              [uu____553]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____552
             in
          uu____547 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___103_579 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___103_579.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___103_579.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____600 = FStar_Syntax_Util.head_and_args t1  in
    match uu____600 with
    | (hd1,args) ->
        let uu____645 =
          let uu____660 =
            let uu____661 = FStar_Syntax_Util.un_uinst hd1  in
            uu____661.FStar_Syntax_Syntax.n  in
          (uu____660, args)  in
        (match uu____645 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____716)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____751 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____751
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____756 ->
             (if w
              then
                (let uu____773 =
                   let uu____779 =
                     let uu____781 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____781
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____779)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____773)
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
    let uu____821 =
      let uu____822 = FStar_Syntax_Subst.compress t  in
      uu____822.FStar_Syntax_Syntax.n  in
    match uu____821 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
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
                FStar_Util.format1 "Not an embedded fvar: %s" uu____844  in
              (FStar_Errors.Warning_NotEmbedded, uu____842)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____836)
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
    let uu____881 =
      let uu____882 = FStar_Syntax_Subst.compress t  in
      uu____882.FStar_Syntax_Syntax.n  in
    match uu____881 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
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
                FStar_Util.format1 "Not an embedded comp: %s" uu____904  in
              (FStar_Errors.Warning_NotEmbedded, uu____902)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____896)
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
    let uu____941 =
      let uu____942 = FStar_Syntax_Subst.compress t  in
      uu____942.FStar_Syntax_Syntax.n  in
    match uu____941 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____948;
          FStar_Syntax_Syntax.rng = uu____949;_}
        ->
        let uu____952 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____952
    | uu____953 ->
        (if w
         then
           (let uu____956 =
              let uu____962 =
                let uu____964 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____964  in
              (FStar_Errors.Warning_NotEmbedded, uu____962)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____956)
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
          let uu____990 =
            let uu____995 =
              let uu____996 =
                let uu____1005 =
                  let uu____1006 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____1006  in
                FStar_Syntax_Syntax.as_arg uu____1005  in
              [uu____996]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____995
             in
          uu____990 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____1026 =
            let uu____1031 =
              let uu____1032 =
                let uu____1041 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____1041  in
              [uu____1032]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____1031
             in
          uu____1026 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____1060 =
            let uu____1065 =
              let uu____1066 =
                let uu____1075 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1075  in
              [uu____1066]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____1065
             in
          uu____1060 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____1093 =
            let uu____1098 =
              let uu____1099 =
                let uu____1108 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____1108  in
              [uu____1099]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____1098
             in
          uu____1093 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___192_1128 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___192_1128.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___192_1128.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1149 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1149 with
    | (hd1,args) ->
        let uu____1194 =
          let uu____1209 =
            let uu____1210 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1210.FStar_Syntax_Syntax.n  in
          (uu____1209, args)  in
        (match uu____1194 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1284)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1319 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1319
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _1326  -> FStar_Pervasives_Native.Some _1326)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1329)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1364 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1364
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _1375  -> FStar_Pervasives_Native.Some _1375)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____1378)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1413 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____1413
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _1420  -> FStar_Pervasives_Native.Some _1420)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _1442  -> FStar_Pervasives_Native.Some _1442)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____1445)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____1480 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____1480
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _1499  -> FStar_Pervasives_Native.Some _1499)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____1500 ->
             (if w
              then
                (let uu____1517 =
                   let uu____1523 =
                     let uu____1525 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1525
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1523)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1517)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1538  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1551 =
            let uu____1556 =
              let uu____1557 =
                let uu____1566 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1566  in
              [uu____1557]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1556
             in
          uu____1551 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
<<<<<<< HEAD
          let uu____1589 =
            let uu____1594 =
              let uu____1595 =
                let uu____1604 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1604  in
              let uu____1605 =
                let uu____1616 =
                  let uu____1625 =
                    let uu____1626 =
                      let uu____1631 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1631  in
                    embed uu____1626 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1625  in
                [uu____1616]  in
              uu____1595 :: uu____1605  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1594
             in
          uu____1589 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1661 =
            let uu____1666 =
              let uu____1667 =
                let uu____1676 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1676  in
              [uu____1667]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1666
             in
          uu____1661 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1694 =
            let uu____1699 =
              let uu____1700 =
                let uu____1709 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1709  in
              [uu____1700]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1699
             in
          uu____1694 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1728 =
            let uu____1733 =
              let uu____1734 =
                let uu____1743 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1743  in
              let uu____1744 =
                let uu____1755 =
                  let uu____1764 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1764  in
                [uu____1755]  in
              uu____1734 :: uu____1744  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1733
             in
          uu____1728 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1807 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1807 with
      | (hd1,args) ->
          let uu____1852 =
            let uu____1865 =
              let uu____1866 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1866.FStar_Syntax_Syntax.n  in
            (uu____1865, args)  in
          (match uu____1852 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1881)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1906 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1906
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _1913  -> FStar_Pervasives_Native.Some _1913)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1916)::(ps,uu____1918)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1953 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1953
                 (fun f1  ->
                    let uu____1959 =
                      let uu____1964 =
                        let uu____1969 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1969  in
                      unembed' w uu____1964 ps  in
                    FStar_Util.bind_opt uu____1959
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _1982  -> FStar_Pervasives_Native.Some _1982)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1987)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____2012 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2012
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2019  -> FStar_Pervasives_Native.Some _2019)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2022)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____2047 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2047
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2054  -> FStar_Pervasives_Native.Some _2054)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____2057)::(t2,uu____2059)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____2094 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2094
                 (fun bv1  ->
                    let uu____2100 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____2100
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _2107  -> FStar_Pervasives_Native.Some _2107)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2108 ->
               (if w
                then
                  (let uu____2123 =
                     let uu____2129 =
                       let uu____2131 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2131
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2129)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2123)
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
    let uu____2158 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2158
=======
    let uu____2176 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2176
>>>>>>> snap
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
<<<<<<< HEAD
    let uu____2173 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2173 e_aqualv
=======
    let uu____2191 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2191 e_aqualv
>>>>>>> snap
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
<<<<<<< HEAD
          let uu____2196 =
            let uu____2201 =
              let uu____2202 =
                let uu____2211 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2211  in
              [uu____2202]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____2201
             in
          uu____2196 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2229 =
            let uu____2234 =
              let uu____2235 =
                let uu____2244 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2244  in
              [uu____2235]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2234
             in
          uu____2229 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2262 =
            let uu____2267 =
              let uu____2268 =
                let uu____2277 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2277  in
              [uu____2268]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2267
             in
          uu____2262 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2296 =
            let uu____2301 =
              let uu____2302 =
                let uu____2311 =
                  let uu____2312 = e_term_aq aq  in embed uu____2312 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2311  in
              let uu____2315 =
                let uu____2326 =
                  let uu____2335 =
                    let uu____2336 = e_argv_aq aq  in embed uu____2336 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2335  in
                [uu____2326]  in
              uu____2302 :: uu____2315  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2301
             in
          uu____2296 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2373 =
            let uu____2378 =
              let uu____2379 =
                let uu____2388 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2388  in
              let uu____2389 =
                let uu____2400 =
                  let uu____2409 =
                    let uu____2410 = e_term_aq aq  in embed uu____2410 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2409  in
                [uu____2400]  in
              uu____2379 :: uu____2389  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2378
             in
          uu____2373 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2439 =
            let uu____2444 =
              let uu____2445 =
                let uu____2454 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2454  in
              let uu____2455 =
                let uu____2466 =
                  let uu____2475 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2475  in
                [uu____2466]  in
              uu____2445 :: uu____2455  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2444
             in
          uu____2439 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2501 =
            let uu____2506 =
              let uu____2507 =
                let uu____2516 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2516  in
              [uu____2507]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2506
             in
          uu____2501 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2535 =
            let uu____2540 =
              let uu____2541 =
                let uu____2550 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2550  in
              let uu____2551 =
                let uu____2562 =
                  let uu____2571 =
                    let uu____2572 = e_term_aq aq  in embed uu____2572 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2571  in
                [uu____2562]  in
              uu____2541 :: uu____2551  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2540
             in
          uu____2535 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2600 =
            let uu____2605 =
              let uu____2606 =
                let uu____2615 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2615  in
              [uu____2606]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2605
             in
          uu____2600 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2634 =
            let uu____2639 =
              let uu____2640 =
                let uu____2649 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2649  in
              let uu____2650 =
                let uu____2661 =
                  let uu____2670 =
=======
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
>>>>>>> snap
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
<<<<<<< HEAD
                  FStar_Syntax_Syntax.as_arg uu____2670  in
                [uu____2661]  in
              uu____2640 :: uu____2650  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2639
             in
          uu____2634 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2705 =
            let uu____2710 =
              let uu____2711 =
                let uu____2720 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2720  in
              let uu____2722 =
                let uu____2733 =
                  let uu____2742 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2742  in
                let uu____2743 =
                  let uu____2754 =
                    let uu____2763 =
                      let uu____2764 = e_term_aq aq  in
                      embed uu____2764 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2763  in
                  let uu____2767 =
                    let uu____2778 =
                      let uu____2787 =
                        let uu____2788 = e_term_aq aq  in
                        embed uu____2788 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2787  in
                    [uu____2778]  in
                  uu____2754 :: uu____2767  in
                uu____2733 :: uu____2743  in
              uu____2711 :: uu____2722  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2710
             in
          uu____2705 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2837 =
            let uu____2842 =
              let uu____2843 =
                let uu____2852 =
                  let uu____2853 = e_term_aq aq  in embed uu____2853 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2852  in
              let uu____2856 =
                let uu____2867 =
                  let uu____2876 =
                    let uu____2877 =
                      let uu____2886 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2886  in
                    embed uu____2877 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2876  in
                [uu____2867]  in
              uu____2843 :: uu____2856  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2842
             in
          uu____2837 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2934 =
            let uu____2939 =
              let uu____2940 =
                let uu____2949 =
                  let uu____2950 = e_term_aq aq  in embed uu____2950 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2949  in
              let uu____2953 =
                let uu____2964 =
                  let uu____2973 =
                    let uu____2974 = e_term_aq aq  in embed uu____2974 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2973  in
                let uu____2977 =
                  let uu____2988 =
                    let uu____2997 =
                      let uu____2998 =
                        let uu____3003 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3003  in
                      embed uu____2998 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2997  in
                  [uu____2988]  in
                uu____2964 :: uu____2977  in
              uu____2940 :: uu____2953  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2939
             in
          uu____2934 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____3047 =
            let uu____3052 =
              let uu____3053 =
                let uu____3062 =
                  let uu____3063 = e_term_aq aq  in embed uu____3063 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3062  in
              let uu____3066 =
                let uu____3077 =
                  let uu____3086 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____3086  in
                let uu____3087 =
                  let uu____3098 =
                    let uu____3107 =
                      let uu____3108 =
                        let uu____3113 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3113  in
                      embed uu____3108 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3107  in
                  [uu____3098]  in
                uu____3077 :: uu____3087  in
              uu____3053 :: uu____3066  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____3052
             in
          uu____3047 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___385_3150 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___385_3150.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___385_3150.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3168 = FStar_Syntax_Util.head_and_args t  in
      match uu____3168 with
      | (hd1,args) ->
          let uu____3213 =
            let uu____3226 =
              let uu____3227 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3227.FStar_Syntax_Syntax.n  in
            (uu____3226, args)  in
          (match uu____3213 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3242)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3267 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3267
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3274  -> FStar_Pervasives_Native.Some _3274)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3277)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3302 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3302
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3309  -> FStar_Pervasives_Native.Some _3309)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3312)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3337 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3337
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _3344  -> FStar_Pervasives_Native.Some _3344)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3347)::(r,uu____3349)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3384 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3384
                 (fun l1  ->
                    let uu____3390 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3390
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _3397  -> FStar_Pervasives_Native.Some _3397)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3400)::(t1,uu____3402)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3437 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3437
                 (fun b1  ->
                    let uu____3443 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3443
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3450  -> FStar_Pervasives_Native.Some _3450)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3453)::(t1,uu____3455)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3490 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3490
                 (fun b1  ->
                    let uu____3496 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3496
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _3503  -> FStar_Pervasives_Native.Some _3503)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3506)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3531 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3531
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _3538  -> FStar_Pervasives_Native.Some _3538)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3541)::(t1,uu____3543)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3578 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3578
                 (fun b1  ->
                    let uu____3584 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3584
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3591  -> FStar_Pervasives_Native.Some _3591)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3594)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3619 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3619
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _3626  -> FStar_Pervasives_Native.Some _3626)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3629)::(l,uu____3631)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3666 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3666
=======
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
>>>>>>> snap
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
<<<<<<< HEAD
                      (fun _3675  -> FStar_Pervasives_Native.Some _3675)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3678)::(b,uu____3680)::(t1,uu____3682)::(t2,uu____3684)::[])
=======
                      (fun _3693  -> FStar_Pervasives_Native.Some _3693)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3696)::(b,uu____3698)::(t1,uu____3700)::(t2,uu____3702)::[])
>>>>>>> snap
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
<<<<<<< HEAD
               let uu____3739 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3739
                 (fun r1  ->
                    let uu____3749 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3749
                      (fun b1  ->
                         let uu____3755 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3755
                           (fun t11  ->
                              let uu____3761 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3761
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _3768  ->
                                        FStar_Pervasives_Native.Some _3768)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3772)::(brs,uu____3774)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3809 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3809
                 (fun t2  ->
                    let uu____3815 =
                      let uu____3820 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3820 brs  in
                    FStar_Util.bind_opt uu____3815
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _3835  -> FStar_Pervasives_Native.Some _3835)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3840)::(t1,uu____3842)::(tacopt,uu____3844)::[])
=======
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
>>>>>>> snap
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
<<<<<<< HEAD
               let uu____3889 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3889
                 (fun e1  ->
                    let uu____3895 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3895
                      (fun t2  ->
                         let uu____3901 =
                           let uu____3906 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3906 tacopt  in
                         FStar_Util.bind_opt uu____3901
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _3921  ->
                                   FStar_Pervasives_Native.Some _3921)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3926)::(c,uu____3928)::(tacopt,uu____3930)::[])
=======
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
>>>>>>> snap
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
<<<<<<< HEAD
               let uu____3975 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3975
                 (fun e1  ->
                    let uu____3981 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3981
                      (fun c1  ->
                         let uu____3987 =
                           let uu____3992 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3992 tacopt  in
                         FStar_Util.bind_opt uu____3987
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4007  ->
                                   FStar_Pervasives_Native.Some _4007)
=======
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
>>>>>>> snap
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
<<<<<<< HEAD
                 (fun _4027  -> FStar_Pervasives_Native.Some _4027)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____4028 ->
               (if w
                then
                  (let uu____4043 =
                     let uu____4049 =
                       let uu____4051 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4051
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4049)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____4043)
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
    let uu____4080 =
      let uu____4085 =
        let uu____4086 =
          let uu____4095 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____4095  in
        let uu____4097 =
          let uu____4108 =
            let uu____4117 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4117  in
          let uu____4118 =
            let uu____4129 =
              let uu____4138 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4138  in
            [uu____4129]  in
          uu____4108 :: uu____4118  in
        uu____4086 :: uu____4097  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4085
       in
    uu____4080 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4189 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4189 with
    | (hd1,args) ->
        let uu____4234 =
          let uu____4247 =
            let uu____4248 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4248.FStar_Syntax_Syntax.n  in
          (uu____4247, args)  in
        (match uu____4234 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4263)::(idx,uu____4265)::(s,uu____4267)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4312 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4312
               (fun nm1  ->
                  let uu____4322 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4322
                    (fun idx1  ->
                       let uu____4328 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4328
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _4335  ->
                                 FStar_Pervasives_Native.Some _4335)
=======
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
>>>>>>> snap
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
<<<<<<< HEAD
         | uu____4336 ->
             (if w
              then
                (let uu____4351 =
                   let uu____4357 =
                     let uu____4359 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4359
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4357)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4351)
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
        let uu____4385 =
          let uu____4390 =
            let uu____4391 =
              let uu____4400 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4400  in
            let uu____4401 =
              let uu____4412 =
                let uu____4421 =
                  let uu____4422 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4422 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4421  in
              [uu____4412]  in
            uu____4391 :: uu____4401  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4390
           in
        uu____4385 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4458 =
          let uu____4463 =
            let uu____4464 =
              let uu____4473 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4473  in
            let uu____4474 =
              let uu____4485 =
                let uu____4494 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4494  in
              [uu____4485]  in
            uu____4464 :: uu____4474  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4463
           in
        uu____4458 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___606_4519 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___606_4519.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___606_4519.FStar_Syntax_Syntax.vars)
=======
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
>>>>>>> snap
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
<<<<<<< HEAD
    let uu____4538 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4538 with
    | (hd1,args) ->
        let uu____4583 =
          let uu____4596 =
            let uu____4597 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4597.FStar_Syntax_Syntax.n  in
          (uu____4596, args)  in
        (match uu____4583 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4612)::(md,uu____4614)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4649 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4649
               (fun t3  ->
                  let uu____4655 =
                    let uu____4660 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4660 md  in
                  FStar_Util.bind_opt uu____4655
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _4675  -> FStar_Pervasives_Native.Some _4675)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4680)::(post,uu____4682)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4717 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4717
               (fun pre1  ->
                  let uu____4723 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4723
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _4730  -> FStar_Pervasives_Native.Some _4730)
=======
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
>>>>>>> snap
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
<<<<<<< HEAD
               (fun _4748  -> FStar_Pervasives_Native.Some _4748)
               FStar_Reflection_Data.C_Unknown
         | uu____4749 ->
             (if w
              then
                (let uu____4764 =
                   let uu____4770 =
                     let uu____4772 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4772
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4770)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4764)
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
    let uu___653_4797 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___653_4797.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___653_4797.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4818 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4818 with
    | (hd1,args) ->
        let uu____4863 =
          let uu____4878 =
            let uu____4879 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4879.FStar_Syntax_Syntax.n  in
          (uu____4878, args)  in
        (match uu____4863 with
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
         | uu____4951 ->
             (if w
              then
                (let uu____4968 =
                   let uu____4974 =
                     let uu____4976 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4976
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4974)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4968)
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
    let uu____5013 =
      let uu____5014 = FStar_Syntax_Subst.compress t  in
      uu____5014.FStar_Syntax_Syntax.n  in
    match uu____5013 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5020;
          FStar_Syntax_Syntax.rng = uu____5021;_}
        ->
        let uu____5024 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5024
    | uu____5025 ->
        (if w
         then
           (let uu____5028 =
              let uu____5034 =
                let uu____5036 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5036
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5034)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5028)
=======
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
>>>>>>> snap
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
<<<<<<< HEAD
  let embed_ident i rng uu____5076 uu____5077 =
    let uu____5079 =
      let uu____5085 = FStar_Ident.range_of_id i  in
      let uu____5086 = FStar_Ident.text_of_id i  in (uu____5085, uu____5086)
       in
    embed repr rng uu____5079  in
  let unembed_ident t w uu____5113 =
    let uu____5118 = unembed' w repr t  in
    match uu____5118 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5142 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5142
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5149 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5149
=======
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
>>>>>>> snap
  
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
<<<<<<< HEAD
        let uu____5188 =
          let uu____5193 =
            let uu____5194 =
              let uu____5203 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5203  in
            let uu____5205 =
              let uu____5216 =
                let uu____5225 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5225  in
              let uu____5226 =
                let uu____5237 =
                  let uu____5246 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5246  in
                let uu____5249 =
                  let uu____5260 =
                    let uu____5269 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5269  in
                  let uu____5270 =
                    let uu____5281 =
                      let uu____5290 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5290  in
                    [uu____5281]  in
                  uu____5260 :: uu____5270  in
                uu____5237 :: uu____5249  in
              uu____5216 :: uu____5226  in
            uu____5194 :: uu____5205  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5193
           in
        uu____5188 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5341 =
          let uu____5346 =
            let uu____5347 =
              let uu____5356 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5356  in
            let uu____5360 =
              let uu____5371 =
                let uu____5380 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5380  in
              [uu____5371]  in
            uu____5347 :: uu____5360  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5346
           in
        uu____5341 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5422 =
          let uu____5427 =
            let uu____5428 =
              let uu____5437 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5437  in
            let uu____5441 =
              let uu____5452 =
                let uu____5461 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5461  in
              let uu____5464 =
                let uu____5475 =
                  let uu____5484 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5484  in
                let uu____5485 =
                  let uu____5496 =
                    let uu____5505 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5505  in
                  let uu____5506 =
                    let uu____5517 =
                      let uu____5526 =
                        let uu____5527 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5527 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5526  in
                    [uu____5517]  in
                  uu____5496 :: uu____5506  in
                uu____5475 :: uu____5485  in
              uu____5452 :: uu____5464  in
            uu____5428 :: uu____5441  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5427
           in
        uu____5422 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___729_5591 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___729_5591.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___729_5591.FStar_Syntax_Syntax.vars)
=======
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
>>>>>>> snap
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
<<<<<<< HEAD
    let uu____5610 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5610 with
    | (hd1,args) ->
        let uu____5655 =
          let uu____5668 =
            let uu____5669 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5669.FStar_Syntax_Syntax.n  in
          (uu____5668, args)  in
        (match uu____5655 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5684)::(us,uu____5686)::(bs,uu____5688)::(t2,uu____5690)::
            (dcs,uu____5692)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5757 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5757
               (fun nm1  ->
                  let uu____5775 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5775
                    (fun us1  ->
                       let uu____5789 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5789
                         (fun bs1  ->
                            let uu____5795 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5795
                              (fun t3  ->
                                 let uu____5801 =
                                   let uu____5809 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5809 dcs  in
                                 FStar_Util.bind_opt uu____5801
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _5839  ->
                                           FStar_Pervasives_Native.Some _5839)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5848)::(fvar1,uu____5850)::(univs1,uu____5852)::
            (ty,uu____5854)::(t2,uu____5856)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5921 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5921
               (fun r1  ->
                  let uu____5931 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5931
                    (fun fvar2  ->
                       let uu____5937 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5937
                         (fun univs2  ->
                            let uu____5951 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____5951
                              (fun ty1  ->
                                 let uu____5957 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____5957
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _5964  ->
                                           FStar_Pervasives_Native.Some _5964)
=======
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
>>>>>>> snap
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
<<<<<<< HEAD
         | uu____5983 ->
             (if w
              then
                (let uu____5998 =
                   let uu____6004 =
                     let uu____6006 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6006
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6004)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5998)
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
          let uu____6032 =
            let uu____6037 =
              let uu____6038 =
                let uu____6047 =
                  let uu____6048 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6048  in
                FStar_Syntax_Syntax.as_arg uu____6047  in
              [uu____6038]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6037
             in
          uu____6032 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6068 =
            let uu____6073 =
              let uu____6074 =
                let uu____6083 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6083  in
              let uu____6084 =
                let uu____6095 =
                  let uu____6104 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6104  in
                [uu____6095]  in
              uu____6074 :: uu____6084  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6073
             in
          uu____6068 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___804_6129 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___804_6129.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___804_6129.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6150 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6150 with
    | (hd1,args) ->
        let uu____6195 =
          let uu____6208 =
            let uu____6209 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6209.FStar_Syntax_Syntax.n  in
          (uu____6208, args)  in
        (match uu____6195 with
=======
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
>>>>>>> snap
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
<<<<<<< HEAD
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6239)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6264 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6264
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _6271  -> FStar_Pervasives_Native.Some _6271)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6274)::(e2,uu____6276)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6311 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6311
               (fun e11  ->
                  let uu____6317 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6317
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _6324  -> FStar_Pervasives_Native.Some _6324)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6325 ->
             (if w
              then
                (let uu____6340 =
                   let uu____6346 =
                     let uu____6348 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6348
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6346)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6340)
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
    let uu____6379 = FStar_Ident.path_of_lid lid  in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____6379  in
  let unembed1 w t =
    let uu____6407 = unembed' w FStar_Syntax_Embeddings.e_string_list t  in
    FStar_Util.map_opt uu____6407
      (fun p  -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos)
     in
  let uu____6424 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x  -> fun r  -> fun uu____6431  -> fun uu____6432  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____6439  -> unembed1 w x) uu____6424
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
          let uu____6462 =
            let uu____6467 =
              let uu____6468 =
                let uu____6477 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6477  in
              [uu____6468]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
              uu____6467
             in
          uu____6462 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Discriminator l ->
          let uu____6495 =
            let uu____6500 =
              let uu____6501 =
                let uu____6510 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6510  in
              [uu____6501]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
              uu____6500
             in
          uu____6495 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Action l ->
          let uu____6528 =
            let uu____6533 =
              let uu____6534 =
                let uu____6543 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6543  in
              [uu____6534]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
              uu____6533
             in
          uu____6528 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Projector (l,i) ->
          let uu____6562 =
            let uu____6567 =
              let uu____6568 =
                let uu____6577 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6577  in
              let uu____6578 =
                let uu____6589 =
                  let uu____6598 = embed e_ident rng i  in
                  FStar_Syntax_Syntax.as_arg uu____6598  in
                [uu____6589]  in
              uu____6568 :: uu____6578  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
              uu____6567
             in
          uu____6562 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.RecordType (ids1,ids2) ->
          let uu____6633 =
            let uu____6638 =
              let uu____6639 =
                let uu____6648 =
                  let uu____6649 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6649 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6648  in
              let uu____6656 =
                let uu____6667 =
                  let uu____6676 =
                    let uu____6677 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6677 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6676  in
                [uu____6667]  in
              uu____6639 :: uu____6656  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
              uu____6638
             in
          uu____6633 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.RecordConstructor (ids1,ids2) ->
          let uu____6718 =
            let uu____6723 =
              let uu____6724 =
                let uu____6733 =
                  let uu____6734 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6734 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6733  in
              let uu____6741 =
                let uu____6752 =
                  let uu____6761 =
                    let uu____6762 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6762 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6761  in
                [uu____6752]  in
              uu____6724 :: uu____6741  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
              uu____6723
             in
          uu____6718 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___894_6793 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___894_6793.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___894_6793.FStar_Syntax_Syntax.vars)
    }  in
  let unembed1 w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6814 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6814 with
    | (hd1,args) ->
        let uu____6859 =
          let uu____6872 =
            let uu____6873 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6873.FStar_Syntax_Syntax.n  in
          (uu____6872, args)  in
        (match uu____6859 with
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7158)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7183 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7183
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7190  -> FStar_Pervasives_Native.Some _7190)
                    (FStar_Syntax_Syntax.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7193)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7218 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7218
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7225  -> FStar_Pervasives_Native.Some _7225)
                    (FStar_Syntax_Syntax.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7228)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7253 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7253
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7260  -> FStar_Pervasives_Native.Some _7260)
                    (FStar_Syntax_Syntax.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7263)::(i,uu____7265)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7300 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7300
               (fun l1  ->
                  let uu____7306 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7306
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun _7313  -> FStar_Pervasives_Native.Some _7313)
                         (FStar_Syntax_Syntax.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7316)::(ids2,uu____7318)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7353 =
               let uu____7358 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7358 ids1  in
             FStar_Util.bind_opt uu____7353
               (fun ids11  ->
                  let uu____7372 =
                    let uu____7377 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7377 ids2  in
                  FStar_Util.bind_opt uu____7372
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7392  -> FStar_Pervasives_Native.Some _7392)
                         (FStar_Syntax_Syntax.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7399)::(ids2,uu____7401)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____7436 =
               let uu____7441 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7441 ids1  in
             FStar_Util.bind_opt uu____7436
               (fun ids11  ->
                  let uu____7455 =
                    let uu____7460 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7460 ids2  in
                  FStar_Util.bind_opt uu____7455
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7475  -> FStar_Pervasives_Native.Some _7475)
                         (FStar_Syntax_Syntax.RecordConstructor
                            (ids11, ids21))))
         | uu____7480 ->
             (if w
              then
                (let uu____7495 =
                   let uu____7501 =
                     let uu____7503 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____7503
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____7501)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7495)
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
    let uu____7521 =
      let uu____7526 =
        let uu____7527 =
          let uu____7536 =
            let uu____7537 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____7537  in
          FStar_Syntax_Syntax.as_arg uu____7536  in
        [uu____7527]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____7526
       in
    uu____7521 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
=======
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
>>>>>>> snap
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
<<<<<<< HEAD
    let uu____7561 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____7561 with
    | (bv,aq) ->
        let uu____7568 =
          let uu____7573 =
            let uu____7574 =
              let uu____7583 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____7583  in
            let uu____7584 =
              let uu____7595 =
                let uu____7604 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____7604  in
              [uu____7595]  in
            uu____7574 :: uu____7584  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____7573
           in
        uu____7568 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
=======
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
>>>>>>> snap
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
<<<<<<< HEAD
    let uu____7636 =
      let uu____7641 =
        let uu____7642 =
          let uu____7651 =
            let uu____7652 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____7659 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____7652 i.FStar_Syntax_Syntax.rng uu____7659  in
          FStar_Syntax_Syntax.as_arg uu____7651  in
        [uu____7642]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____7641
       in
    uu____7636 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
=======
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
>>>>>>> snap
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
<<<<<<< HEAD
    let uu____7689 =
      let uu____7694 =
        let uu____7695 =
          let uu____7704 =
            let uu____7705 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____7705  in
          FStar_Syntax_Syntax.as_arg uu____7704  in
        [uu____7695]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____7694
       in
    uu____7689 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
=======
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
>>>>>>> snap
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_optionstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
<<<<<<< HEAD
    let uu____7741 =
      let uu____7746 =
        let uu____7747 =
          let uu____7756 =
            let uu____7757 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____7757  in
          FStar_Syntax_Syntax.as_arg uu____7756  in
        [uu____7747]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____7746
       in
    uu____7741 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
=======
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
>>>>>>> snap
  