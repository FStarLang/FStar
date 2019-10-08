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
          let uu____1599 =
            let uu____1604 =
              let uu____1605 =
                let uu____1614 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1614  in
              let uu____1615 =
                let uu____1626 =
                  let uu____1635 =
                    let uu____1636 =
                      let uu____1646 =
                        let uu____1654 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_tuple2 uu____1654
                          FStar_Syntax_Embeddings.e_bool
                         in
                      FStar_Syntax_Embeddings.e_list uu____1646  in
                    embed uu____1636 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1635  in
                [uu____1626]  in
              uu____1605 :: uu____1615  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1604
             in
          uu____1599 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1695 =
            let uu____1700 =
              let uu____1701 =
                let uu____1710 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1710  in
              [uu____1701]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1700
             in
          uu____1695 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1728 =
            let uu____1733 =
              let uu____1734 =
                let uu____1743 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1743  in
              [uu____1734]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1733
             in
          uu____1728 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1762 =
            let uu____1767 =
              let uu____1768 =
                let uu____1777 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1777  in
              let uu____1778 =
                let uu____1789 =
                  let uu____1798 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1798  in
                [uu____1789]  in
              uu____1768 :: uu____1778  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1767
             in
          uu____1762 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1841 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1841 with
      | (hd1,args) ->
          let uu____1886 =
            let uu____1899 =
              let uu____1900 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1900.FStar_Syntax_Syntax.n  in
            (uu____1899, args)  in
          (match uu____1886 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1915)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1940 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1940
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _1947  -> FStar_Pervasives_Native.Some _1947)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1950)::(ps,uu____1952)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1987 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1987
                 (fun f1  ->
                    let uu____1993 =
                      let uu____2003 =
                        let uu____2013 =
                          let uu____2021 = e_pattern' ()  in
                          FStar_Syntax_Embeddings.e_tuple2 uu____2021
                            FStar_Syntax_Embeddings.e_bool
                           in
                        FStar_Syntax_Embeddings.e_list uu____2013  in
                      unembed' w uu____2003 ps  in
                    FStar_Util.bind_opt uu____1993
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _2055  -> FStar_Pervasives_Native.Some _2055)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2065)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____2090 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2090
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2097  -> FStar_Pervasives_Native.Some _2097)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2100)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____2125 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2125
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2132  -> FStar_Pervasives_Native.Some _2132)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____2135)::(t2,uu____2137)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____2172 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2172
                 (fun bv1  ->
                    let uu____2178 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____2178
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _2185  -> FStar_Pervasives_Native.Some _2185)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2186 ->
               (if w
                then
                  (let uu____2201 =
                     let uu____2207 =
                       let uu____2209 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2209
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2207)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2201)
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
    let uu____2236 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2236
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2251 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2251 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2274 =
            let uu____2279 =
              let uu____2280 =
                let uu____2289 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2289  in
              [uu____2280]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____2279
             in
          uu____2274 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2307 =
            let uu____2312 =
              let uu____2313 =
                let uu____2322 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2322  in
              [uu____2313]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2312
             in
          uu____2307 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2340 =
            let uu____2345 =
              let uu____2346 =
                let uu____2355 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2355  in
              [uu____2346]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2345
             in
          uu____2340 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2374 =
            let uu____2379 =
              let uu____2380 =
                let uu____2389 =
                  let uu____2390 = e_term_aq aq  in embed uu____2390 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2389  in
              let uu____2393 =
                let uu____2404 =
                  let uu____2413 =
                    let uu____2414 = e_argv_aq aq  in embed uu____2414 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2413  in
                [uu____2404]  in
              uu____2380 :: uu____2393  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2379
             in
          uu____2374 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2451 =
            let uu____2456 =
              let uu____2457 =
                let uu____2466 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2466  in
              let uu____2467 =
                let uu____2478 =
                  let uu____2487 =
                    let uu____2488 = e_term_aq aq  in embed uu____2488 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2487  in
                [uu____2478]  in
              uu____2457 :: uu____2467  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2456
             in
          uu____2451 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2517 =
            let uu____2522 =
              let uu____2523 =
                let uu____2532 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2532  in
              let uu____2533 =
                let uu____2544 =
                  let uu____2553 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2553  in
                [uu____2544]  in
              uu____2523 :: uu____2533  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2522
             in
          uu____2517 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2579 =
            let uu____2584 =
              let uu____2585 =
                let uu____2594 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2594  in
              [uu____2585]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2584
             in
          uu____2579 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2613 =
            let uu____2618 =
              let uu____2619 =
                let uu____2628 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2628  in
              let uu____2629 =
                let uu____2640 =
                  let uu____2649 =
                    let uu____2650 = e_term_aq aq  in embed uu____2650 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2649  in
                [uu____2640]  in
              uu____2619 :: uu____2629  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2618
             in
          uu____2613 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2678 =
            let uu____2683 =
              let uu____2684 =
                let uu____2693 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2693  in
              [uu____2684]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2683
             in
          uu____2678 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2712 =
            let uu____2717 =
              let uu____2718 =
                let uu____2727 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2727  in
              let uu____2728 =
                let uu____2739 =
                  let uu____2748 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2748  in
                [uu____2739]  in
              uu____2718 :: uu____2728  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2717
             in
          uu____2712 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2783 =
            let uu____2788 =
              let uu____2789 =
                let uu____2798 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2798  in
              let uu____2800 =
                let uu____2811 =
                  let uu____2820 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2820  in
                let uu____2821 =
                  let uu____2832 =
                    let uu____2841 =
                      let uu____2842 = e_term_aq aq  in
                      embed uu____2842 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2841  in
                  let uu____2845 =
                    let uu____2856 =
                      let uu____2865 =
                        let uu____2866 = e_term_aq aq  in
                        embed uu____2866 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2865  in
                    [uu____2856]  in
                  uu____2832 :: uu____2845  in
                uu____2811 :: uu____2821  in
              uu____2789 :: uu____2800  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2788
             in
          uu____2783 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2915 =
            let uu____2920 =
              let uu____2921 =
                let uu____2930 =
                  let uu____2931 = e_term_aq aq  in embed uu____2931 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2930  in
              let uu____2934 =
                let uu____2945 =
                  let uu____2954 =
                    let uu____2955 =
                      let uu____2964 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2964  in
                    embed uu____2955 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2954  in
                [uu____2945]  in
              uu____2921 :: uu____2934  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2920
             in
          uu____2915 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____3012 =
            let uu____3017 =
              let uu____3018 =
                let uu____3027 =
                  let uu____3028 = e_term_aq aq  in embed uu____3028 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3027  in
              let uu____3031 =
                let uu____3042 =
                  let uu____3051 =
                    let uu____3052 = e_term_aq aq  in embed uu____3052 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____3051  in
                let uu____3055 =
                  let uu____3066 =
                    let uu____3075 =
                      let uu____3076 =
                        let uu____3081 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3081  in
                      embed uu____3076 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3075  in
                  [uu____3066]  in
                uu____3042 :: uu____3055  in
              uu____3018 :: uu____3031  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____3017
             in
          uu____3012 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____3125 =
            let uu____3130 =
              let uu____3131 =
                let uu____3140 =
                  let uu____3141 = e_term_aq aq  in embed uu____3141 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3140  in
              let uu____3144 =
                let uu____3155 =
                  let uu____3164 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____3164  in
                let uu____3165 =
                  let uu____3176 =
                    let uu____3185 =
                      let uu____3186 =
                        let uu____3191 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3191  in
                      embed uu____3186 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3185  in
                  [uu____3176]  in
                uu____3155 :: uu____3165  in
              uu____3131 :: uu____3144  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____3130
             in
          uu____3125 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___385_3228 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___385_3228.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___385_3228.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3246 = FStar_Syntax_Util.head_and_args t  in
      match uu____3246 with
      | (hd1,args) ->
          let uu____3291 =
            let uu____3304 =
              let uu____3305 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3305.FStar_Syntax_Syntax.n  in
            (uu____3304, args)  in
          (match uu____3291 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3320)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3345 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3345
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3352  -> FStar_Pervasives_Native.Some _3352)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3355)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3380 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3380
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3387  -> FStar_Pervasives_Native.Some _3387)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3390)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3415 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3415
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _3422  -> FStar_Pervasives_Native.Some _3422)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3425)::(r,uu____3427)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3462 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3462
                 (fun l1  ->
                    let uu____3468 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3468
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _3475  -> FStar_Pervasives_Native.Some _3475)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3478)::(t1,uu____3480)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3515 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3515
                 (fun b1  ->
                    let uu____3521 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3521
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3528  -> FStar_Pervasives_Native.Some _3528)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3531)::(t1,uu____3533)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3568 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3568
                 (fun b1  ->
                    let uu____3574 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3574
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _3581  -> FStar_Pervasives_Native.Some _3581)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3584)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3609 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3609
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _3616  -> FStar_Pervasives_Native.Some _3616)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3619)::(t1,uu____3621)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3656 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3656
                 (fun b1  ->
                    let uu____3662 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3662
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3669  -> FStar_Pervasives_Native.Some _3669)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3672)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3697 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3697
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _3704  -> FStar_Pervasives_Native.Some _3704)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3707)::(l,uu____3709)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3744 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3744
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _3753  -> FStar_Pervasives_Native.Some _3753)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3756)::(b,uu____3758)::(t1,uu____3760)::(t2,uu____3762)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3817 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3817
                 (fun r1  ->
                    let uu____3827 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3827
                      (fun b1  ->
                         let uu____3833 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3833
                           (fun t11  ->
                              let uu____3839 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3839
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _3846  ->
                                        FStar_Pervasives_Native.Some _3846)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3850)::(brs,uu____3852)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3887 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3887
                 (fun t2  ->
                    let uu____3893 =
                      let uu____3898 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3898 brs  in
                    FStar_Util.bind_opt uu____3893
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _3913  -> FStar_Pervasives_Native.Some _3913)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3918)::(t1,uu____3920)::(tacopt,uu____3922)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3967 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3967
                 (fun e1  ->
                    let uu____3973 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3973
                      (fun t2  ->
                         let uu____3979 =
                           let uu____3984 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3984 tacopt  in
                         FStar_Util.bind_opt uu____3979
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _3999  ->
                                   FStar_Pervasives_Native.Some _3999)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____4004)::(c,uu____4006)::(tacopt,uu____4008)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____4053 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4053
                 (fun e1  ->
                    let uu____4059 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____4059
                      (fun c1  ->
                         let uu____4065 =
                           let uu____4070 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4070 tacopt  in
                         FStar_Util.bind_opt uu____4065
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4085  ->
                                   FStar_Pervasives_Native.Some _4085)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _4105  -> FStar_Pervasives_Native.Some _4105)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____4106 ->
               (if w
                then
                  (let uu____4121 =
                     let uu____4127 =
                       let uu____4129 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4129
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4127)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____4121)
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
    let uu____4158 =
      let uu____4163 =
        let uu____4164 =
          let uu____4173 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____4173  in
        let uu____4175 =
          let uu____4186 =
            let uu____4195 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4195  in
          let uu____4196 =
            let uu____4207 =
              let uu____4216 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4216  in
            [uu____4207]  in
          uu____4186 :: uu____4196  in
        uu____4164 :: uu____4175  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4163
       in
    uu____4158 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4267 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4267 with
    | (hd1,args) ->
        let uu____4312 =
          let uu____4325 =
            let uu____4326 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4326.FStar_Syntax_Syntax.n  in
          (uu____4325, args)  in
        (match uu____4312 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4341)::(idx,uu____4343)::(s,uu____4345)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4390 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4390
               (fun nm1  ->
                  let uu____4400 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4400
                    (fun idx1  ->
                       let uu____4406 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4406
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _4413  ->
                                 FStar_Pervasives_Native.Some _4413)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4414 ->
             (if w
              then
                (let uu____4429 =
                   let uu____4435 =
                     let uu____4437 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4437
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4435)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4429)
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
        let uu____4463 =
          let uu____4468 =
            let uu____4469 =
              let uu____4478 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4478  in
            let uu____4479 =
              let uu____4490 =
                let uu____4499 =
                  let uu____4500 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4500 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4499  in
              [uu____4490]  in
            uu____4469 :: uu____4479  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4468
           in
        uu____4463 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4536 =
          let uu____4541 =
            let uu____4542 =
              let uu____4551 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4551  in
            let uu____4552 =
              let uu____4563 =
                let uu____4572 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4572  in
              [uu____4563]  in
            uu____4542 :: uu____4552  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4541
           in
        uu____4536 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___606_4597 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___606_4597.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___606_4597.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4616 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4616 with
    | (hd1,args) ->
        let uu____4661 =
          let uu____4674 =
            let uu____4675 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4675.FStar_Syntax_Syntax.n  in
          (uu____4674, args)  in
        (match uu____4661 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4690)::(md,uu____4692)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4727 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4727
               (fun t3  ->
                  let uu____4733 =
                    let uu____4738 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4738 md  in
                  FStar_Util.bind_opt uu____4733
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _4753  -> FStar_Pervasives_Native.Some _4753)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4758)::(post,uu____4760)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4795 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4795
               (fun pre1  ->
                  let uu____4801 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4801
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _4808  -> FStar_Pervasives_Native.Some _4808)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _4826  -> FStar_Pervasives_Native.Some _4826)
               FStar_Reflection_Data.C_Unknown
         | uu____4827 ->
             (if w
              then
                (let uu____4842 =
                   let uu____4848 =
                     let uu____4850 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4850
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4848)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4842)
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
    let uu___653_4875 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___653_4875.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___653_4875.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4896 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4896 with
    | (hd1,args) ->
        let uu____4941 =
          let uu____4956 =
            let uu____4957 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4957.FStar_Syntax_Syntax.n  in
          (uu____4956, args)  in
        (match uu____4941 with
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
         | uu____5029 ->
             (if w
              then
                (let uu____5046 =
                   let uu____5052 =
                     let uu____5054 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____5054
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5052)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5046)
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
    let uu____5091 =
      let uu____5092 = FStar_Syntax_Subst.compress t  in
      uu____5092.FStar_Syntax_Syntax.n  in
    match uu____5091 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5098;
          FStar_Syntax_Syntax.rng = uu____5099;_}
        ->
        let uu____5102 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5102
    | uu____5103 ->
        (if w
         then
           (let uu____5106 =
              let uu____5112 =
                let uu____5114 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5114
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5112)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5106)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____5154 uu____5155 =
    let uu____5157 =
      let uu____5163 = FStar_Ident.range_of_id i  in
      let uu____5164 = FStar_Ident.text_of_id i  in (uu____5163, uu____5164)
       in
    embed repr rng uu____5157  in
  let unembed_ident t w uu____5191 =
    let uu____5196 = unembed' w repr t  in
    match uu____5196 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5220 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5220
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5227 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5227
  
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
        let uu____5266 =
          let uu____5271 =
            let uu____5272 =
              let uu____5281 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5281  in
            let uu____5283 =
              let uu____5294 =
                let uu____5303 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5303  in
              let uu____5304 =
                let uu____5315 =
                  let uu____5324 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5324  in
                let uu____5327 =
                  let uu____5338 =
                    let uu____5347 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5347  in
                  let uu____5348 =
                    let uu____5359 =
                      let uu____5368 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5368  in
                    [uu____5359]  in
                  uu____5338 :: uu____5348  in
                uu____5315 :: uu____5327  in
              uu____5294 :: uu____5304  in
            uu____5272 :: uu____5283  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5271
           in
        uu____5266 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5419 =
          let uu____5424 =
            let uu____5425 =
              let uu____5434 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5434  in
            let uu____5438 =
              let uu____5449 =
                let uu____5458 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5458  in
              [uu____5449]  in
            uu____5425 :: uu____5438  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5424
           in
        uu____5419 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5500 =
          let uu____5505 =
            let uu____5506 =
              let uu____5515 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5515  in
            let uu____5519 =
              let uu____5530 =
                let uu____5539 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5539  in
              let uu____5542 =
                let uu____5553 =
                  let uu____5562 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5562  in
                let uu____5563 =
                  let uu____5574 =
                    let uu____5583 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5583  in
                  let uu____5584 =
                    let uu____5595 =
                      let uu____5604 =
                        let uu____5605 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5605 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5604  in
                    [uu____5595]  in
                  uu____5574 :: uu____5584  in
                uu____5553 :: uu____5563  in
              uu____5530 :: uu____5542  in
            uu____5506 :: uu____5519  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5505
           in
        uu____5500 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___729_5669 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___729_5669.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___729_5669.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5688 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5688 with
    | (hd1,args) ->
        let uu____5733 =
          let uu____5746 =
            let uu____5747 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5747.FStar_Syntax_Syntax.n  in
          (uu____5746, args)  in
        (match uu____5733 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5762)::(us,uu____5764)::(bs,uu____5766)::(t2,uu____5768)::
            (dcs,uu____5770)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5835 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5835
               (fun nm1  ->
                  let uu____5853 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5853
                    (fun us1  ->
                       let uu____5867 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5867
                         (fun bs1  ->
                            let uu____5873 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5873
                              (fun t3  ->
                                 let uu____5879 =
                                   let uu____5887 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5887 dcs  in
                                 FStar_Util.bind_opt uu____5879
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _5917  ->
                                           FStar_Pervasives_Native.Some _5917)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5926)::(fvar1,uu____5928)::(univs1,uu____5930)::
            (ty,uu____5932)::(t2,uu____5934)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5999 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5999
               (fun r1  ->
                  let uu____6009 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____6009
                    (fun fvar2  ->
                       let uu____6015 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____6015
                         (fun univs2  ->
                            let uu____6029 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____6029
                              (fun ty1  ->
                                 let uu____6035 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____6035
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _6042  ->
                                           FStar_Pervasives_Native.Some _6042)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6061 ->
             (if w
              then
                (let uu____6076 =
                   let uu____6082 =
                     let uu____6084 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6084
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6082)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6076)
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
          let uu____6110 =
            let uu____6115 =
              let uu____6116 =
                let uu____6125 =
                  let uu____6126 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6126  in
                FStar_Syntax_Syntax.as_arg uu____6125  in
              [uu____6116]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6115
             in
          uu____6110 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6146 =
            let uu____6151 =
              let uu____6152 =
                let uu____6161 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6161  in
              let uu____6162 =
                let uu____6173 =
                  let uu____6182 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6182  in
                [uu____6173]  in
              uu____6152 :: uu____6162  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6151
             in
          uu____6146 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___804_6207 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___804_6207.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___804_6207.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6228 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6228 with
    | (hd1,args) ->
        let uu____6273 =
          let uu____6286 =
            let uu____6287 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6287.FStar_Syntax_Syntax.n  in
          (uu____6286, args)  in
        (match uu____6273 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6317)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6342 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6342
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _6349  -> FStar_Pervasives_Native.Some _6349)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6352)::(e2,uu____6354)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6389 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6389
               (fun e11  ->
                  let uu____6395 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6395
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _6402  -> FStar_Pervasives_Native.Some _6402)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6403 ->
             (if w
              then
                (let uu____6418 =
                   let uu____6424 =
                     let uu____6426 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6426
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6424)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6418)
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
    let uu____6457 = FStar_Ident.path_of_lid lid  in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____6457  in
  let unembed1 w t =
    let uu____6485 = unembed' w FStar_Syntax_Embeddings.e_string_list t  in
    FStar_Util.map_opt uu____6485
      (fun p  -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos)
     in
  let uu____6502 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x  -> fun r  -> fun uu____6509  -> fun uu____6510  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____6517  -> unembed1 w x) uu____6502
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
          let uu____6540 =
            let uu____6545 =
              let uu____6546 =
                let uu____6555 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6555  in
              [uu____6546]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
              uu____6545
             in
          uu____6540 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Discriminator l ->
          let uu____6573 =
            let uu____6578 =
              let uu____6579 =
                let uu____6588 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6588  in
              [uu____6579]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
              uu____6578
             in
          uu____6573 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Action l ->
          let uu____6606 =
            let uu____6611 =
              let uu____6612 =
                let uu____6621 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6621  in
              [uu____6612]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
              uu____6611
             in
          uu____6606 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Projector (l,i) ->
          let uu____6640 =
            let uu____6645 =
              let uu____6646 =
                let uu____6655 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6655  in
              let uu____6656 =
                let uu____6667 =
                  let uu____6676 = embed e_ident rng i  in
                  FStar_Syntax_Syntax.as_arg uu____6676  in
                [uu____6667]  in
              uu____6646 :: uu____6656  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
              uu____6645
             in
          uu____6640 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.RecordType (ids1,ids2) ->
          let uu____6711 =
            let uu____6716 =
              let uu____6717 =
                let uu____6726 =
                  let uu____6727 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6727 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6726  in
              let uu____6734 =
                let uu____6745 =
                  let uu____6754 =
                    let uu____6755 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6755 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6754  in
                [uu____6745]  in
              uu____6717 :: uu____6734  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
              uu____6716
             in
          uu____6711 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.RecordConstructor (ids1,ids2) ->
          let uu____6796 =
            let uu____6801 =
              let uu____6802 =
                let uu____6811 =
                  let uu____6812 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6812 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6811  in
              let uu____6819 =
                let uu____6830 =
                  let uu____6839 =
                    let uu____6840 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6840 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6839  in
                [uu____6830]  in
              uu____6802 :: uu____6819  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
              uu____6801
             in
          uu____6796 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___894_6871 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___894_6871.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___894_6871.FStar_Syntax_Syntax.vars)
    }  in
  let unembed1 w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6892 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6892 with
    | (hd1,args) ->
        let uu____6937 =
          let uu____6950 =
            let uu____6951 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6951.FStar_Syntax_Syntax.n  in
          (uu____6950, args)  in
        (match uu____6937 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7236)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7261 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7261
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7268  -> FStar_Pervasives_Native.Some _7268)
                    (FStar_Syntax_Syntax.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7271)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7296 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7296
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7303  -> FStar_Pervasives_Native.Some _7303)
                    (FStar_Syntax_Syntax.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7306)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7331 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7331
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7338  -> FStar_Pervasives_Native.Some _7338)
                    (FStar_Syntax_Syntax.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7341)::(i,uu____7343)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7378 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7378
               (fun l1  ->
                  let uu____7384 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7384
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun _7391  -> FStar_Pervasives_Native.Some _7391)
                         (FStar_Syntax_Syntax.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7394)::(ids2,uu____7396)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7431 =
               let uu____7436 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7436 ids1  in
             FStar_Util.bind_opt uu____7431
               (fun ids11  ->
                  let uu____7450 =
                    let uu____7455 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7455 ids2  in
                  FStar_Util.bind_opt uu____7450
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7470  -> FStar_Pervasives_Native.Some _7470)
                         (FStar_Syntax_Syntax.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7477)::(ids2,uu____7479)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____7514 =
               let uu____7519 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7519 ids1  in
             FStar_Util.bind_opt uu____7514
               (fun ids11  ->
                  let uu____7533 =
                    let uu____7538 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7538 ids2  in
                  FStar_Util.bind_opt uu____7533
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7553  -> FStar_Pervasives_Native.Some _7553)
                         (FStar_Syntax_Syntax.RecordConstructor
                            (ids11, ids21))))
         | uu____7558 ->
             (if w
              then
                (let uu____7573 =
                   let uu____7579 =
                     let uu____7581 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____7581
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____7579)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7573)
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
    let uu____7599 =
      let uu____7604 =
        let uu____7605 =
          let uu____7614 =
            let uu____7615 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____7615  in
          FStar_Syntax_Syntax.as_arg uu____7614  in
        [uu____7605]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____7604
       in
    uu____7599 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7639 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____7639 with
    | (bv,aq) ->
        let uu____7646 =
          let uu____7651 =
            let uu____7652 =
              let uu____7661 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____7661  in
            let uu____7662 =
              let uu____7673 =
                let uu____7682 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____7682  in
              [uu____7673]  in
            uu____7652 :: uu____7662  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____7651
           in
        uu____7646 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7714 =
      let uu____7719 =
        let uu____7720 =
          let uu____7729 =
            let uu____7730 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____7737 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____7730 i.FStar_Syntax_Syntax.rng uu____7737  in
          FStar_Syntax_Syntax.as_arg uu____7729  in
        [uu____7720]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____7719
       in
    uu____7714 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7767 =
      let uu____7772 =
        let uu____7773 =
          let uu____7782 =
            let uu____7783 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____7783  in
          FStar_Syntax_Syntax.as_arg uu____7782  in
        [uu____7773]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____7772
       in
    uu____7767 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
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
    let uu____7819 =
      let uu____7824 =
        let uu____7825 =
          let uu____7834 =
            let uu____7835 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____7835  in
          FStar_Syntax_Syntax.as_arg uu____7834  in
        [uu____7825]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____7824
       in
    uu____7819 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  