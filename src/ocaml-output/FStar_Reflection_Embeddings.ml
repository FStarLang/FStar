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
=======
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
>>>>>>> snap
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
<<<<<<< HEAD
                     uu____2141)
>>>>>>> snap
=======
                     uu____2201)
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
<<<<<<< HEAD
    let uu____2158 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2158
=======
    let uu____2176 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2176
>>>>>>> snap
=======
    let uu____2236 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2236
>>>>>>> snap
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
<<<<<<< HEAD
<<<<<<< HEAD
    let uu____2173 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2173 e_aqualv
=======
    let uu____2191 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2191 e_aqualv
>>>>>>> snap
=======
    let uu____2251 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2251 e_aqualv
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
=======
          let uu____2274 =
            let uu____2279 =
              let uu____2280 =
                let uu____2289 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2289  in
              [uu____2280]  in
>>>>>>> snap
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
<<<<<<< HEAD
                FStar_Syntax_Syntax.as_arg uu____2667  in
              let uu____2668 =
                let uu____2679 =
                  let uu____2688 =
>>>>>>> snap
=======
                FStar_Syntax_Syntax.as_arg uu____2727  in
              let uu____2728 =
                let uu____2739 =
                  let uu____2748 =
>>>>>>> snap
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
<<<<<<< HEAD
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
=======
                  FStar_Syntax_Syntax.as_arg uu____2748  in
                [uu____2739]  in
              uu____2718 :: uu____2728  in
>>>>>>> snap
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2717
             in
          uu____2712 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,attrs,b,t1,t2) ->
          let uu____2788 =
            let uu____2793 =
              let uu____2794 =
                let uu____2803 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2803  in
              let uu____2805 =
                let uu____2816 =
                  let uu____2825 =
                    let uu____2826 = FStar_Syntax_Embeddings.e_list e_term
                       in
                    embed uu____2826 rng attrs  in
                  FStar_Syntax_Syntax.as_arg uu____2825  in
                let uu____2833 =
                  let uu____2844 =
                    let uu____2853 = embed e_bv rng b  in
                    FStar_Syntax_Syntax.as_arg uu____2853  in
                  let uu____2854 =
                    let uu____2865 =
                      let uu____2874 =
                        let uu____2875 = e_term_aq aq  in
                        embed uu____2875 rng t1  in
                      FStar_Syntax_Syntax.as_arg uu____2874  in
                    let uu____2878 =
                      let uu____2889 =
                        let uu____2898 =
                          let uu____2899 = e_term_aq aq  in
                          embed uu____2899 rng t2  in
                        FStar_Syntax_Syntax.as_arg uu____2898  in
                      [uu____2889]  in
                    uu____2865 :: uu____2878  in
                  uu____2844 :: uu____2854  in
                uu____2816 :: uu____2833  in
              uu____2794 :: uu____2805  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2793
             in
          uu____2788 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2956 =
            let uu____2961 =
              let uu____2962 =
                let uu____2971 =
                  let uu____2972 = e_term_aq aq  in embed uu____2972 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2971  in
              let uu____2975 =
                let uu____2986 =
                  let uu____2995 =
                    let uu____2996 =
                      let uu____3005 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____3005  in
                    embed uu____2996 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2995  in
                [uu____2986]  in
              uu____2962 :: uu____2975  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2961
             in
          uu____2956 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____3053 =
            let uu____3058 =
              let uu____3059 =
                let uu____3068 =
                  let uu____3069 = e_term_aq aq  in embed uu____3069 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3068  in
              let uu____3072 =
                let uu____3083 =
                  let uu____3092 =
                    let uu____3093 = e_term_aq aq  in embed uu____3093 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____3092  in
                let uu____3096 =
                  let uu____3107 =
                    let uu____3116 =
                      let uu____3117 =
                        let uu____3122 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3122  in
                      embed uu____3117 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3116  in
                  [uu____3107]  in
                uu____3083 :: uu____3096  in
              uu____3059 :: uu____3072  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____3058
             in
          uu____3053 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____3166 =
            let uu____3171 =
              let uu____3172 =
                let uu____3181 =
                  let uu____3182 = e_term_aq aq  in embed uu____3182 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3181  in
              let uu____3185 =
                let uu____3196 =
                  let uu____3205 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____3205  in
                let uu____3206 =
                  let uu____3217 =
                    let uu____3226 =
                      let uu____3227 =
                        let uu____3232 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3232  in
                      embed uu____3227 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3226  in
                  [uu____3217]  in
                uu____3196 :: uu____3206  in
              uu____3172 :: uu____3185  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____3171
             in
          uu____3166 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___386_3269 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___386_3269.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___386_3269.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3287 = FStar_Syntax_Util.head_and_args t  in
      match uu____3287 with
      | (hd1,args) ->
          let uu____3332 =
            let uu____3345 =
              let uu____3346 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3346.FStar_Syntax_Syntax.n  in
            (uu____3345, args)  in
          (match uu____3332 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3361)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3386 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3386
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3393  -> FStar_Pervasives_Native.Some _3393)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3396)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3421 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3421
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3428  -> FStar_Pervasives_Native.Some _3428)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3431)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3456 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3456
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _3463  -> FStar_Pervasives_Native.Some _3463)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3466)::(r,uu____3468)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3503 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3503
                 (fun l1  ->
                    let uu____3509 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3509
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _3516  -> FStar_Pervasives_Native.Some _3516)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3519)::(t1,uu____3521)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3556 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3556
                 (fun b1  ->
                    let uu____3562 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3562
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3569  -> FStar_Pervasives_Native.Some _3569)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3572)::(t1,uu____3574)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3609 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3609
                 (fun b1  ->
                    let uu____3615 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3615
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _3622  -> FStar_Pervasives_Native.Some _3622)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3625)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3650 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3650
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _3657  -> FStar_Pervasives_Native.Some _3657)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3660)::(t1,uu____3662)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3697 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3697
                 (fun b1  ->
                    let uu____3703 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3703
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3710  -> FStar_Pervasives_Native.Some _3710)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3713)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3738 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3738
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _3745  -> FStar_Pervasives_Native.Some _3745)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3748)::(l,uu____3750)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3785 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
<<<<<<< HEAD
<<<<<<< HEAD
               FStar_Util.bind_opt uu____3684
>>>>>>> snap
=======
               FStar_Util.bind_opt uu____3744
>>>>>>> snap
=======
               FStar_Util.bind_opt uu____3785
>>>>>>> snap
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
                      (fun _3753  -> FStar_Pervasives_Native.Some _3753)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3756)::(b,uu____3758)::(t1,uu____3760)::(t2,uu____3762)::[])
>>>>>>> snap
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
<<<<<<< HEAD
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
=======
               let uu____3817 = unembed' w FStar_Syntax_Embeddings.e_bool r
>>>>>>> snap
=======
                      (fun _3794  -> FStar_Pervasives_Native.Some _3794)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3797)::(attrs,uu____3799)::(b,uu____3801)::
              (t1,uu____3803)::(t2,uu____3805)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3870 = unembed' w FStar_Syntax_Embeddings.e_bool r
>>>>>>> snap
                  in
               FStar_Util.bind_opt uu____3870
                 (fun r1  ->
                    let uu____3880 =
                      let uu____3885 = FStar_Syntax_Embeddings.e_list e_term
                         in
                      unembed' w uu____3885 attrs  in
                    FStar_Util.bind_opt uu____3880
                      (fun attrs1  ->
                         let uu____3899 = unembed' w e_bv b  in
                         FStar_Util.bind_opt uu____3899
                           (fun b1  ->
                              let uu____3905 = unembed' w e_term t1  in
                              FStar_Util.bind_opt uu____3905
                                (fun t11  ->
                                   let uu____3911 = unembed' w e_term t2  in
                                   FStar_Util.bind_opt uu____3911
                                     (fun t21  ->
                                        FStar_All.pipe_left
                                          (fun _3918  ->
                                             FStar_Pervasives_Native.Some
                                               _3918)
                                          (FStar_Reflection_Data.Tv_Let
                                             (r1, attrs1, b1, t11, t21)))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3924)::(brs,uu____3926)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3961 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3961
                 (fun t2  ->
                    let uu____3967 =
                      let uu____3972 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3972 brs  in
                    FStar_Util.bind_opt uu____3967
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _3987  -> FStar_Pervasives_Native.Some _3987)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
<<<<<<< HEAD
<<<<<<< HEAD
              fv,(e,uu____3858)::(t1,uu____3860)::(tacopt,uu____3862)::[])
>>>>>>> snap
=======
              fv,(e,uu____3918)::(t1,uu____3920)::(tacopt,uu____3922)::[])
>>>>>>> snap
=======
              fv,(e,uu____3992)::(t1,uu____3994)::(tacopt,uu____3996)::[])
>>>>>>> snap
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
               let uu____3967 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3967
>>>>>>> snap
=======
               let uu____4041 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4041
>>>>>>> snap
                 (fun e1  ->
                    let uu____4047 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____4047
                      (fun t2  ->
                         let uu____4053 =
                           let uu____4058 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4058 tacopt  in
                         FStar_Util.bind_opt uu____4053
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4073  ->
                                   FStar_Pervasives_Native.Some _4073)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
<<<<<<< HEAD
<<<<<<< HEAD
              fv,(e,uu____3944)::(c,uu____3946)::(tacopt,uu____3948)::[])
>>>>>>> snap
=======
              fv,(e,uu____4004)::(c,uu____4006)::(tacopt,uu____4008)::[])
>>>>>>> snap
=======
              fv,(e,uu____4078)::(c,uu____4080)::(tacopt,uu____4082)::[])
>>>>>>> snap
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
               let uu____4053 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4053
>>>>>>> snap
=======
               let uu____4127 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4127
>>>>>>> snap
                 (fun e1  ->
                    let uu____4133 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____4133
                      (fun c1  ->
                         let uu____4139 =
                           let uu____4144 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4144 tacopt  in
                         FStar_Util.bind_opt uu____4139
                           (fun tacopt1  ->
                              FStar_All.pipe_left
<<<<<<< HEAD
<<<<<<< HEAD
                                (fun _4025  ->
                                   FStar_Pervasives_Native.Some _4025)
>>>>>>> snap
=======
                                (fun _4085  ->
                                   FStar_Pervasives_Native.Some _4085)
>>>>>>> snap
=======
                                (fun _4159  ->
                                   FStar_Pervasives_Native.Some _4159)
>>>>>>> snap
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
                 (fun _4105  -> FStar_Pervasives_Native.Some _4105)
>>>>>>> snap
=======
                 (fun _4179  -> FStar_Pervasives_Native.Some _4179)
>>>>>>> snap
                 FStar_Reflection_Data.Tv_Unknown
           | uu____4180 ->
               (if w
                then
                  (let uu____4195 =
                     let uu____4201 =
                       let uu____4203 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4203
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4201)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
<<<<<<< HEAD
                     uu____4061)
>>>>>>> snap
=======
                     uu____4121)
>>>>>>> snap
=======
                     uu____4195)
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
<<<<<<< HEAD
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
=======
    let uu____4158 =
      let uu____4163 =
        let uu____4164 =
          let uu____4173 =
>>>>>>> snap
=======
    let uu____4232 =
      let uu____4237 =
        let uu____4238 =
          let uu____4247 =
>>>>>>> snap
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____4247  in
        let uu____4249 =
          let uu____4260 =
            let uu____4269 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4269  in
          let uu____4270 =
            let uu____4281 =
              let uu____4290 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4290  in
            [uu____4281]  in
          uu____4260 :: uu____4270  in
        uu____4238 :: uu____4249  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4237
       in
    uu____4232 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4341 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4341 with
    | (hd1,args) ->
        let uu____4386 =
          let uu____4399 =
            let uu____4400 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4400.FStar_Syntax_Syntax.n  in
          (uu____4399, args)  in
        (match uu____4386 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4415)::(idx,uu____4417)::(s,uu____4419)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4464 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4464
               (fun nm1  ->
                  let uu____4474 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4474
                    (fun idx1  ->
                       let uu____4480 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4480
                         (fun s1  ->
                            FStar_All.pipe_left
<<<<<<< HEAD
<<<<<<< HEAD
                              (fun _4353  ->
                                 FStar_Pervasives_Native.Some _4353)
>>>>>>> snap
=======
                              (fun _4413  ->
                                 FStar_Pervasives_Native.Some _4413)
>>>>>>> snap
=======
                              (fun _4487  ->
                                 FStar_Pervasives_Native.Some _4487)
>>>>>>> snap
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
         | uu____4414 ->
>>>>>>> snap
=======
         | uu____4488 ->
>>>>>>> snap
             (if w
              then
                (let uu____4503 =
                   let uu____4509 =
                     let uu____4511 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4511
                      in
<<<<<<< HEAD
<<<<<<< HEAD
                   (FStar_Errors.Warning_NotEmbedded, uu____4375)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4369)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____4435)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4429)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____4509)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4503)
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
<<<<<<< HEAD
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
=======
        let uu____4463 =
          let uu____4468 =
            let uu____4469 =
              let uu____4478 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4478  in
            let uu____4479 =
              let uu____4490 =
                let uu____4499 =
                  let uu____4500 = FStar_Syntax_Embeddings.e_option e_term
>>>>>>> snap
=======
        let uu____4537 =
          let uu____4542 =
            let uu____4543 =
              let uu____4552 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4552  in
            let uu____4553 =
              let uu____4564 =
                let uu____4573 =
                  let uu____4574 = FStar_Syntax_Embeddings.e_option e_term
>>>>>>> snap
                     in
                  embed uu____4574 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4573  in
              [uu____4564]  in
            uu____4543 :: uu____4553  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4542
           in
        uu____4537 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4610 =
          let uu____4615 =
            let uu____4616 =
              let uu____4625 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4625  in
            let uu____4626 =
              let uu____4637 =
                let uu____4646 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4646  in
              [uu____4637]  in
            uu____4616 :: uu____4626  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4615
           in
        uu____4610 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___611_4671 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___611_4671.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
<<<<<<< HEAD
<<<<<<< HEAD
          FStar_Syntax_Syntax.vars = (uu___591_4537.FStar_Syntax_Syntax.vars)
>>>>>>> snap
=======
          FStar_Syntax_Syntax.vars = (uu___606_4597.FStar_Syntax_Syntax.vars)
>>>>>>> snap
=======
          FStar_Syntax_Syntax.vars = (uu___611_4671.FStar_Syntax_Syntax.vars)
>>>>>>> snap
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
    let uu____4616 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4616 with
>>>>>>> snap
=======
    let uu____4690 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4690 with
>>>>>>> snap
    | (hd1,args) ->
        let uu____4735 =
          let uu____4748 =
            let uu____4749 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4749.FStar_Syntax_Syntax.n  in
          (uu____4748, args)  in
        (match uu____4735 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4764)::(md,uu____4766)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4801 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4801
               (fun t3  ->
                  let uu____4807 =
                    let uu____4812 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4812 md  in
                  FStar_Util.bind_opt uu____4807
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _4827  -> FStar_Pervasives_Native.Some _4827)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4832)::(post,uu____4834)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4869 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4869
               (fun pre1  ->
                  let uu____4875 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4875
                    (fun post1  ->
                       FStar_All.pipe_left
<<<<<<< HEAD
<<<<<<< HEAD
                         (fun _4748  -> FStar_Pervasives_Native.Some _4748)
>>>>>>> snap
=======
                         (fun _4808  -> FStar_Pervasives_Native.Some _4808)
>>>>>>> snap
=======
                         (fun _4882  -> FStar_Pervasives_Native.Some _4882)
>>>>>>> snap
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
               (fun _4826  -> FStar_Pervasives_Native.Some _4826)
>>>>>>> snap
=======
               (fun _4900  -> FStar_Pervasives_Native.Some _4900)
>>>>>>> snap
               FStar_Reflection_Data.C_Unknown
         | uu____4901 ->
             (if w
              then
                (let uu____4916 =
                   let uu____4922 =
                     let uu____4924 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4924
                      in
<<<<<<< HEAD
<<<<<<< HEAD
                   (FStar_Errors.Warning_NotEmbedded, uu____4788)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4782)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____4848)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4842)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____4922)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4916)
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
<<<<<<< HEAD
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
=======
    let uu___653_4875 = r  in
>>>>>>> snap
=======
    let uu___658_4949 = r  in
>>>>>>> snap
    {
      FStar_Syntax_Syntax.n = (uu___658_4949.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___658_4949.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4970 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4970 with
    | (hd1,args) ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____4881 =
          let uu____4896 =
            let uu____4897 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4897.FStar_Syntax_Syntax.n  in
          (uu____4896, args)  in
        (match uu____4881 with
>>>>>>> snap
=======
        let uu____4941 =
          let uu____4956 =
            let uu____4957 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4957.FStar_Syntax_Syntax.n  in
          (uu____4956, args)  in
        (match uu____4941 with
>>>>>>> snap
=======
        let uu____5015 =
          let uu____5030 =
            let uu____5031 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5031.FStar_Syntax_Syntax.n  in
          (uu____5030, args)  in
        (match uu____5015 with
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
<<<<<<< HEAD
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
=======
         | uu____5029 ->
>>>>>>> snap
=======
         | uu____5103 ->
>>>>>>> snap
             (if w
              then
                (let uu____5120 =
                   let uu____5126 =
                     let uu____5128 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____5128
                      in
<<<<<<< HEAD
<<<<<<< HEAD
                   (FStar_Errors.Warning_NotEmbedded, uu____4992)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4986)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____5052)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5046)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____5126)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5120)
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
<<<<<<< HEAD
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
=======
    let uu____5091 =
      let uu____5092 = FStar_Syntax_Subst.compress t  in
      uu____5092.FStar_Syntax_Syntax.n  in
    match uu____5091 with
>>>>>>> snap
=======
    let uu____5165 =
      let uu____5166 = FStar_Syntax_Subst.compress t  in
      uu____5166.FStar_Syntax_Syntax.n  in
    match uu____5165 with
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5172;
          FStar_Syntax_Syntax.rng = uu____5173;_}
        ->
        let uu____5176 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5176
    | uu____5177 ->
        (if w
         then
           (let uu____5180 =
              let uu____5186 =
                let uu____5188 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5188
                 in
<<<<<<< HEAD
<<<<<<< HEAD
              (FStar_Errors.Warning_NotEmbedded, uu____5052)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5046)
>>>>>>> snap
=======
              (FStar_Errors.Warning_NotEmbedded, uu____5112)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5106)
>>>>>>> snap
=======
              (FStar_Errors.Warning_NotEmbedded, uu____5186)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5180)
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
<<<<<<< HEAD
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
=======
  let embed_ident i rng uu____5154 uu____5155 =
    let uu____5157 =
      let uu____5163 = FStar_Ident.range_of_id i  in
      let uu____5164 = FStar_Ident.text_of_id i  in (uu____5163, uu____5164)
>>>>>>> snap
=======
  let embed_ident i rng uu____5228 uu____5229 =
    let uu____5231 =
      let uu____5237 = FStar_Ident.range_of_id i  in
      let uu____5238 = FStar_Ident.text_of_id i  in (uu____5237, uu____5238)
>>>>>>> snap
       in
    embed repr rng uu____5231  in
  let unembed_ident t w uu____5265 =
    let uu____5270 = unembed' w repr t  in
    match uu____5270 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5294 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5294
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5301 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
<<<<<<< HEAD
<<<<<<< HEAD
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5167
>>>>>>> snap
=======
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5227
>>>>>>> snap
=======
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5301
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
<<<<<<< HEAD
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
=======
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
>>>>>>> snap
=======
        let uu____5340 =
          let uu____5345 =
            let uu____5346 =
              let uu____5355 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5355  in
            let uu____5357 =
              let uu____5368 =
                let uu____5377 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5377  in
              let uu____5378 =
                let uu____5389 =
                  let uu____5398 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5398  in
                let uu____5401 =
                  let uu____5412 =
                    let uu____5421 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5421  in
                  let uu____5422 =
                    let uu____5433 =
                      let uu____5442 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5442  in
                    [uu____5433]  in
                  uu____5412 :: uu____5422  in
                uu____5389 :: uu____5401  in
              uu____5368 :: uu____5378  in
            uu____5346 :: uu____5357  in
>>>>>>> snap
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5345
           in
        uu____5340 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5493 =
          let uu____5498 =
            let uu____5499 =
              let uu____5508 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5508  in
            let uu____5512 =
              let uu____5523 =
                let uu____5532 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5532  in
              [uu____5523]  in
            uu____5499 :: uu____5512  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5498
           in
        uu____5493 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5574 =
          let uu____5579 =
            let uu____5580 =
              let uu____5589 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5589  in
            let uu____5593 =
              let uu____5604 =
                let uu____5613 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5613  in
              let uu____5616 =
                let uu____5627 =
                  let uu____5636 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5636  in
                let uu____5637 =
                  let uu____5648 =
                    let uu____5657 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5657  in
                  let uu____5658 =
                    let uu____5669 =
                      let uu____5678 =
                        let uu____5679 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5679 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5678  in
                    [uu____5669]  in
                  uu____5648 :: uu____5658  in
                uu____5627 :: uu____5637  in
              uu____5604 :: uu____5616  in
            uu____5580 :: uu____5593  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5579
           in
        uu____5574 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___734_5743 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___734_5743.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
<<<<<<< HEAD
<<<<<<< HEAD
          FStar_Syntax_Syntax.vars = (uu___714_5609.FStar_Syntax_Syntax.vars)
>>>>>>> snap
=======
          FStar_Syntax_Syntax.vars = (uu___729_5669.FStar_Syntax_Syntax.vars)
>>>>>>> snap
=======
          FStar_Syntax_Syntax.vars = (uu___734_5743.FStar_Syntax_Syntax.vars)
>>>>>>> snap
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
    let uu____5688 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5688 with
>>>>>>> snap
=======
    let uu____5762 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5762 with
>>>>>>> snap
    | (hd1,args) ->
        let uu____5807 =
          let uu____5820 =
            let uu____5821 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5821.FStar_Syntax_Syntax.n  in
          (uu____5820, args)  in
        (match uu____5807 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5836)::(us,uu____5838)::(bs,uu____5840)::(t2,uu____5842)::
            (dcs,uu____5844)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5909 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5909
               (fun nm1  ->
                  let uu____5927 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5927
                    (fun us1  ->
                       let uu____5941 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5941
                         (fun bs1  ->
                            let uu____5947 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5947
                              (fun t3  ->
                                 let uu____5953 =
                                   let uu____5961 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5961 dcs  in
                                 FStar_Util.bind_opt uu____5953
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _5991  ->
                                           FStar_Pervasives_Native.Some _5991)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____6000)::(fvar1,uu____6002)::(univs1,uu____6004)::
            (ty,uu____6006)::(t2,uu____6008)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____6073 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____6073
               (fun r1  ->
                  let uu____6083 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____6083
                    (fun fvar2  ->
                       let uu____6089 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____6089
                         (fun univs2  ->
                            let uu____6103 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____6103
                              (fun ty1  ->
                                 let uu____6109 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____6109
                                   (fun t3  ->
                                      FStar_All.pipe_left
<<<<<<< HEAD
<<<<<<< HEAD
                                        (fun _5982  ->
                                           FStar_Pervasives_Native.Some _5982)
>>>>>>> snap
=======
                                        (fun _6042  ->
                                           FStar_Pervasives_Native.Some _6042)
>>>>>>> snap
=======
                                        (fun _6116  ->
                                           FStar_Pervasives_Native.Some _6116)
>>>>>>> snap
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
         | uu____6061 ->
>>>>>>> snap
=======
         | uu____6135 ->
>>>>>>> snap
             (if w
              then
                (let uu____6150 =
                   let uu____6156 =
                     let uu____6158 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6158
                      in
<<<<<<< HEAD
<<<<<<< HEAD
                   (FStar_Errors.Warning_NotEmbedded, uu____6022)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6016)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____6082)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6076)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____6156)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6150)
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
<<<<<<< HEAD
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
=======
          let uu____6110 =
            let uu____6115 =
              let uu____6116 =
                let uu____6125 =
                  let uu____6126 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6126  in
                FStar_Syntax_Syntax.as_arg uu____6125  in
              [uu____6116]  in
>>>>>>> snap
=======
          let uu____6184 =
            let uu____6189 =
              let uu____6190 =
                let uu____6199 =
                  let uu____6200 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6200  in
                FStar_Syntax_Syntax.as_arg uu____6199  in
              [uu____6190]  in
>>>>>>> snap
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6189
             in
          uu____6184 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6220 =
            let uu____6225 =
              let uu____6226 =
                let uu____6235 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6235  in
              let uu____6236 =
                let uu____6247 =
                  let uu____6256 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6256  in
                [uu____6247]  in
              uu____6226 :: uu____6236  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6225
             in
          uu____6220 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___809_6281 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___809_6281.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___809_6281.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6302 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6302 with
    | (hd1,args) ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____6213 =
          let uu____6226 =
            let uu____6227 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6227.FStar_Syntax_Syntax.n  in
          (uu____6226, args)  in
        (match uu____6213 with
>>>>>>> snap
=======
        let uu____6273 =
          let uu____6286 =
            let uu____6287 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6287.FStar_Syntax_Syntax.n  in
          (uu____6286, args)  in
        (match uu____6273 with
>>>>>>> snap
=======
        let uu____6347 =
          let uu____6360 =
            let uu____6361 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6361.FStar_Syntax_Syntax.n  in
          (uu____6360, args)  in
        (match uu____6347 with
>>>>>>> snap
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6317)::[]) when
>>>>>>> snap
=======
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6391)::[]) when
>>>>>>> snap
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6416 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6416
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _6423  -> FStar_Pervasives_Native.Some _6423)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6426)::(e2,uu____6428)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6463 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6463
               (fun e11  ->
                  let uu____6469 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6469
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _6476  -> FStar_Pervasives_Native.Some _6476)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6477 ->
             (if w
              then
                (let uu____6492 =
                   let uu____6498 =
                     let uu____6500 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6500
                      in
<<<<<<< HEAD
<<<<<<< HEAD
                   (FStar_Errors.Warning_NotEmbedded, uu____6364)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6358)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____6424)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6418)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____6498)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6492)
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
<<<<<<< HEAD
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
=======
    let uu____6457 = FStar_Ident.path_of_lid lid  in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____6457  in
>>>>>>> snap
=======
    let uu____6531 = FStar_Ident.path_of_lid lid  in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____6531  in
>>>>>>> snap
  let unembed1 w t =
    let uu____6559 = unembed' w FStar_Syntax_Embeddings.e_string_list t  in
    FStar_Util.map_opt uu____6559
      (fun p  -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos)
     in
  let uu____6576 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb_full
<<<<<<< HEAD
<<<<<<< HEAD
    (fun x  -> fun r  -> fun uu____6449  -> fun uu____6450  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____6457  -> unembed1 w x) uu____6442
>>>>>>> snap
=======
    (fun x  -> fun r  -> fun uu____6509  -> fun uu____6510  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____6517  -> unembed1 w x) uu____6502
>>>>>>> snap
=======
    (fun x  -> fun r  -> fun uu____6583  -> fun uu____6584  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____6591  -> unembed1 w x) uu____6576
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
<<<<<<< HEAD
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
=======
          let uu____6540 =
            let uu____6545 =
              let uu____6546 =
                let uu____6555 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6555  in
              [uu____6546]  in
>>>>>>> snap
=======
          let uu____6614 =
            let uu____6619 =
              let uu____6620 =
                let uu____6629 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6629  in
              [uu____6620]  in
>>>>>>> snap
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
              uu____6619
             in
          uu____6614 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Discriminator l ->
          let uu____6647 =
            let uu____6652 =
              let uu____6653 =
                let uu____6662 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6662  in
              [uu____6653]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
              uu____6652
             in
          uu____6647 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Action l ->
          let uu____6680 =
            let uu____6685 =
              let uu____6686 =
                let uu____6695 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6695  in
              [uu____6686]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
              uu____6685
             in
          uu____6680 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.Projector (l,i) ->
          let uu____6714 =
            let uu____6719 =
              let uu____6720 =
                let uu____6729 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6729  in
              let uu____6730 =
                let uu____6741 =
                  let uu____6750 = embed e_ident rng i  in
                  FStar_Syntax_Syntax.as_arg uu____6750  in
                [uu____6741]  in
              uu____6720 :: uu____6730  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
              uu____6719
             in
          uu____6714 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.RecordType (ids1,ids2) ->
          let uu____6785 =
            let uu____6790 =
              let uu____6791 =
                let uu____6800 =
                  let uu____6801 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6801 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6800  in
              let uu____6808 =
                let uu____6819 =
                  let uu____6828 =
                    let uu____6829 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6829 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6828  in
                [uu____6819]  in
              uu____6791 :: uu____6808  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
              uu____6790
             in
          uu____6785 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Syntax_Syntax.RecordConstructor (ids1,ids2) ->
          let uu____6870 =
            let uu____6875 =
              let uu____6876 =
                let uu____6885 =
                  let uu____6886 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6886 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6885  in
              let uu____6893 =
                let uu____6904 =
                  let uu____6913 =
                    let uu____6914 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6914 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6913  in
                [uu____6904]  in
              uu____6876 :: uu____6893  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
              uu____6875
             in
          uu____6870 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___899_6945 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___899_6945.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___899_6945.FStar_Syntax_Syntax.vars)
    }  in
  let unembed1 w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6966 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6966 with
    | (hd1,args) ->
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____6877 =
          let uu____6890 =
            let uu____6891 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6891.FStar_Syntax_Syntax.n  in
          (uu____6890, args)  in
        (match uu____6877 with
>>>>>>> snap
=======
        let uu____6937 =
          let uu____6950 =
            let uu____6951 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6951.FStar_Syntax_Syntax.n  in
          (uu____6950, args)  in
        (match uu____6937 with
>>>>>>> snap
=======
        let uu____7011 =
          let uu____7024 =
            let uu____7025 = FStar_Syntax_Util.un_uinst hd1  in
            uu____7025.FStar_Syntax_Syntax.n  in
          (uu____7024, args)  in
        (match uu____7011 with
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
<<<<<<< HEAD
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
=======
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7236)::[]) when
>>>>>>> snap
=======
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7310)::[]) when
>>>>>>> snap
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7335 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7335
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7342  -> FStar_Pervasives_Native.Some _7342)
                    (FStar_Syntax_Syntax.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7345)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7370 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7370
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7377  -> FStar_Pervasives_Native.Some _7377)
                    (FStar_Syntax_Syntax.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7380)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7405 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7405
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7412  -> FStar_Pervasives_Native.Some _7412)
                    (FStar_Syntax_Syntax.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7415)::(i,uu____7417)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7452 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7452
               (fun l1  ->
                  let uu____7458 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7458
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun _7465  -> FStar_Pervasives_Native.Some _7465)
                         (FStar_Syntax_Syntax.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7468)::(ids2,uu____7470)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7505 =
               let uu____7510 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7510 ids1  in
             FStar_Util.bind_opt uu____7505
               (fun ids11  ->
                  let uu____7524 =
                    let uu____7529 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7529 ids2  in
                  FStar_Util.bind_opt uu____7524
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7544  -> FStar_Pervasives_Native.Some _7544)
                         (FStar_Syntax_Syntax.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7551)::(ids2,uu____7553)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____7588 =
               let uu____7593 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7593 ids1  in
             FStar_Util.bind_opt uu____7588
               (fun ids11  ->
                  let uu____7607 =
                    let uu____7612 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7612 ids2  in
                  FStar_Util.bind_opt uu____7607
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7627  -> FStar_Pervasives_Native.Some _7627)
                         (FStar_Syntax_Syntax.RecordConstructor
                            (ids11, ids21))))
         | uu____7632 ->
             (if w
              then
                (let uu____7647 =
                   let uu____7653 =
                     let uu____7655 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____7655
                      in
<<<<<<< HEAD
<<<<<<< HEAD
                   (FStar_Errors.Warning_NotEmbedded, uu____7519)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7513)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____7579)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7573)
>>>>>>> snap
=======
                   (FStar_Errors.Warning_NotEmbedded, uu____7653)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7647)
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
<<<<<<< HEAD
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
=======
    let uu____7599 =
      let uu____7604 =
        let uu____7605 =
          let uu____7614 =
            let uu____7615 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____7615  in
          FStar_Syntax_Syntax.as_arg uu____7614  in
        [uu____7605]  in
>>>>>>> snap
=======
    let uu____7673 =
      let uu____7678 =
        let uu____7679 =
          let uu____7688 =
            let uu____7689 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____7689  in
          FStar_Syntax_Syntax.as_arg uu____7688  in
        [uu____7679]  in
>>>>>>> snap
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____7678
       in
<<<<<<< HEAD
<<<<<<< HEAD
    uu____7539 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
    uu____7599 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
    uu____7673 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
    let uu____7639 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____7639 with
>>>>>>> snap
=======
    let uu____7713 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____7713 with
>>>>>>> snap
    | (bv,aq) ->
        let uu____7720 =
          let uu____7725 =
            let uu____7726 =
              let uu____7735 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____7735  in
            let uu____7736 =
              let uu____7747 =
                let uu____7756 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____7756  in
              [uu____7747]  in
            uu____7726 :: uu____7736  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____7725
           in
<<<<<<< HEAD
<<<<<<< HEAD
        uu____7586 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
        uu____7646 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
        uu____7720 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
    let uu____7714 =
      let uu____7719 =
        let uu____7720 =
          let uu____7729 =
            let uu____7730 =
>>>>>>> snap
=======
    let uu____7788 =
      let uu____7793 =
        let uu____7794 =
          let uu____7803 =
            let uu____7804 =
>>>>>>> snap
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____7811 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____7804 i.FStar_Syntax_Syntax.rng uu____7811  in
          FStar_Syntax_Syntax.as_arg uu____7803  in
        [uu____7794]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____7793
       in
<<<<<<< HEAD
<<<<<<< HEAD
    uu____7654 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
    uu____7714 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
    uu____7788 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
    let uu____7767 =
      let uu____7772 =
        let uu____7773 =
          let uu____7782 =
            let uu____7783 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____7783  in
          FStar_Syntax_Syntax.as_arg uu____7782  in
        [uu____7773]  in
>>>>>>> snap
=======
    let uu____7841 =
      let uu____7846 =
        let uu____7847 =
          let uu____7856 =
            let uu____7857 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____7857  in
          FStar_Syntax_Syntax.as_arg uu____7856  in
        [uu____7847]  in
>>>>>>> snap
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____7846
       in
<<<<<<< HEAD
<<<<<<< HEAD
    uu____7707 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
    uu____7767 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
    uu____7841 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
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
<<<<<<< HEAD
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
=======
    let uu____7819 =
      let uu____7824 =
        let uu____7825 =
          let uu____7834 =
            let uu____7835 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____7835  in
          FStar_Syntax_Syntax.as_arg uu____7834  in
        [uu____7825]  in
>>>>>>> snap
=======
    let uu____7893 =
      let uu____7898 =
        let uu____7899 =
          let uu____7908 =
            let uu____7909 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____7909  in
          FStar_Syntax_Syntax.as_arg uu____7908  in
        [uu____7899]  in
>>>>>>> snap
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____7898
       in
<<<<<<< HEAD
<<<<<<< HEAD
    uu____7753 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
    uu____7819 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
=======
    uu____7893 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
>>>>>>> snap
  