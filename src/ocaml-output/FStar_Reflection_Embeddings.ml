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
  
let (uu___61 : unit) =
  FStar_ST.op_Colon_Equals FStar_Reflection_Basic.e_optionstate_hook
    (FStar_Pervasives_Native.Some e_optionstate)
  
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
          let uu____404 = f x  in
          FStar_Util.bind_opt uu____404
            (fun x1  ->
               let uu____412 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____412
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
        let uu____481 =
          mapM_opt
            (fun uu____494  ->
               match uu____494 with
               | (bv,e) ->
                   let uu____503 = unembed_term w e  in
                   FStar_Util.bind_opt uu____503
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____481
          (fun s  ->
             let uu____517 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____517)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____519 =
        let uu____520 = FStar_Syntax_Subst.compress t1  in
        uu____520.FStar_Syntax_Syntax.n  in
      match uu____519 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____531 ->
          (if w
           then
             (let uu____534 =
                let uu____540 =
                  let uu____542 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____542  in
                (FStar_Errors.Warning_NotEmbedded, uu____540)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____534)
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
          let uu____577 =
            let uu____582 =
              let uu____583 =
                let uu____592 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____592  in
              [uu____583]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____582
             in
          uu____577 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___104_609 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___104_609.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___104_609.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____630 = FStar_Syntax_Util.head_and_args t1  in
    match uu____630 with
    | (hd1,args) ->
        let uu____675 =
          let uu____690 =
            let uu____691 = FStar_Syntax_Util.un_uinst hd1  in
            uu____691.FStar_Syntax_Syntax.n  in
          (uu____690, args)  in
        (match uu____675 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____746)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____781 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____781
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____786 ->
             (if w
              then
                (let uu____803 =
                   let uu____809 =
                     let uu____811 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____811
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____809)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____803)
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
    let uu____851 =
      let uu____852 = FStar_Syntax_Subst.compress t  in
      uu____852.FStar_Syntax_Syntax.n  in
    match uu____851 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____858;
          FStar_Syntax_Syntax.rng = uu____859;_}
        ->
        let uu____862 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____862
    | uu____863 ->
        (if w
         then
           (let uu____866 =
              let uu____872 =
                let uu____874 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____874  in
              (FStar_Errors.Warning_NotEmbedded, uu____872)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____866)
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
    let uu____911 =
      let uu____912 = FStar_Syntax_Subst.compress t  in
      uu____912.FStar_Syntax_Syntax.n  in
    match uu____911 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____918;
          FStar_Syntax_Syntax.rng = uu____919;_}
        ->
        let uu____922 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____922
    | uu____923 ->
        (if w
         then
           (let uu____926 =
              let uu____932 =
                let uu____934 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____934  in
              (FStar_Errors.Warning_NotEmbedded, uu____932)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____926)
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
    let uu____971 =
      let uu____972 = FStar_Syntax_Subst.compress t  in
      uu____972.FStar_Syntax_Syntax.n  in
    match uu____971 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____978;
          FStar_Syntax_Syntax.rng = uu____979;_}
        ->
        let uu____982 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____982
    | uu____983 ->
        (if w
         then
           (let uu____986 =
              let uu____992 =
                let uu____994 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____994  in
              (FStar_Errors.Warning_NotEmbedded, uu____992)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____986)
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
          let uu____1020 =
            let uu____1025 =
              let uu____1026 =
                let uu____1035 =
                  let uu____1036 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____1036  in
                FStar_Syntax_Syntax.as_arg uu____1035  in
              [uu____1026]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____1025
             in
          uu____1020 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____1056 =
            let uu____1061 =
              let uu____1062 =
                let uu____1071 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____1071  in
              [uu____1062]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____1061
             in
          uu____1056 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____1090 =
            let uu____1095 =
              let uu____1096 =
                let uu____1105 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1105  in
              [uu____1096]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____1095
             in
          uu____1090 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____1123 =
            let uu____1128 =
              let uu____1129 =
                let uu____1138 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____1138  in
              [uu____1129]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____1128
             in
          uu____1123 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___193_1158 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___193_1158.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___193_1158.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1179 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1179 with
    | (hd1,args) ->
        let uu____1224 =
          let uu____1239 =
            let uu____1240 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1240.FStar_Syntax_Syntax.n  in
          (uu____1239, args)  in
        (match uu____1224 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1314)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1349 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1349
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _1356  -> FStar_Pervasives_Native.Some _1356)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1359)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1394 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1394
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _1405  -> FStar_Pervasives_Native.Some _1405)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____1408)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1443 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____1443
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _1450  -> FStar_Pervasives_Native.Some _1450)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _1472  -> FStar_Pervasives_Native.Some _1472)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____1475)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____1510 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____1510
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _1529  -> FStar_Pervasives_Native.Some _1529)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____1530 ->
             (if w
              then
                (let uu____1547 =
                   let uu____1553 =
                     let uu____1555 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1555
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1553)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1547)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1568  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1581 =
            let uu____1586 =
              let uu____1587 =
                let uu____1596 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1596  in
              [uu____1587]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1586
             in
          uu____1581 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1629 =
            let uu____1634 =
              let uu____1635 =
                let uu____1644 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1644  in
              let uu____1645 =
                let uu____1656 =
                  let uu____1665 =
                    let uu____1666 =
                      let uu____1676 =
                        let uu____1684 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_tuple2 uu____1684
                          FStar_Syntax_Embeddings.e_bool
                         in
                      FStar_Syntax_Embeddings.e_list uu____1676  in
                    embed uu____1666 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1665  in
                [uu____1656]  in
              uu____1635 :: uu____1645  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1634
             in
          uu____1629 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1725 =
            let uu____1730 =
              let uu____1731 =
                let uu____1740 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1740  in
              [uu____1731]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1730
             in
          uu____1725 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1758 =
            let uu____1763 =
              let uu____1764 =
                let uu____1773 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1773  in
              [uu____1764]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1763
             in
          uu____1758 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1792 =
            let uu____1797 =
              let uu____1798 =
                let uu____1807 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1807  in
              let uu____1808 =
                let uu____1819 =
                  let uu____1828 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1828  in
                [uu____1819]  in
              uu____1798 :: uu____1808  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1797
             in
          uu____1792 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1871 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1871 with
      | (hd1,args) ->
          let uu____1916 =
            let uu____1929 =
              let uu____1930 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1930.FStar_Syntax_Syntax.n  in
            (uu____1929, args)  in
          (match uu____1916 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1945)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1970 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1970
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _1977  -> FStar_Pervasives_Native.Some _1977)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1980)::(ps,uu____1982)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____2017 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____2017
                 (fun f1  ->
                    let uu____2023 =
                      let uu____2033 =
                        let uu____2043 =
                          let uu____2051 = e_pattern' ()  in
                          FStar_Syntax_Embeddings.e_tuple2 uu____2051
                            FStar_Syntax_Embeddings.e_bool
                           in
                        FStar_Syntax_Embeddings.e_list uu____2043  in
                      unembed' w uu____2033 ps  in
                    FStar_Util.bind_opt uu____2023
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _2085  -> FStar_Pervasives_Native.Some _2085)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2095)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____2120 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2120
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2127  -> FStar_Pervasives_Native.Some _2127)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2130)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____2155 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2155
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2162  -> FStar_Pervasives_Native.Some _2162)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____2165)::(t2,uu____2167)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____2202 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2202
                 (fun bv1  ->
                    let uu____2208 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____2208
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _2215  -> FStar_Pervasives_Native.Some _2215)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2216 ->
               (if w
                then
                  (let uu____2231 =
                     let uu____2237 =
                       let uu____2239 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2239
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2237)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2231)
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
let (e_args :
  FStar_Reflection_Data.argv Prims.list FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_list e_argv 
let (e_branch_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2271 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2271
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2286 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2286 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2309 =
            let uu____2314 =
              let uu____2315 =
                let uu____2324 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2324  in
              [uu____2315]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____2314
             in
          uu____2309 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2342 =
            let uu____2347 =
              let uu____2348 =
                let uu____2357 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2357  in
              [uu____2348]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2347
             in
          uu____2342 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2375 =
            let uu____2380 =
              let uu____2381 =
                let uu____2390 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2390  in
              [uu____2381]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2380
             in
          uu____2375 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2409 =
            let uu____2414 =
              let uu____2415 =
                let uu____2424 =
                  let uu____2425 = e_term_aq aq  in embed uu____2425 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2424  in
              let uu____2428 =
                let uu____2439 =
                  let uu____2448 =
                    let uu____2449 = e_argv_aq aq  in embed uu____2449 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2448  in
                [uu____2439]  in
              uu____2415 :: uu____2428  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2414
             in
          uu____2409 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2486 =
            let uu____2491 =
              let uu____2492 =
                let uu____2501 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2501  in
              let uu____2502 =
                let uu____2513 =
                  let uu____2522 =
                    let uu____2523 = e_term_aq aq  in embed uu____2523 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2522  in
                [uu____2513]  in
              uu____2492 :: uu____2502  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2491
             in
          uu____2486 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2552 =
            let uu____2557 =
              let uu____2558 =
                let uu____2567 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2567  in
              let uu____2568 =
                let uu____2579 =
                  let uu____2588 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2588  in
                [uu____2579]  in
              uu____2558 :: uu____2568  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2557
             in
          uu____2552 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2614 =
            let uu____2619 =
              let uu____2620 =
                let uu____2629 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2629  in
              [uu____2620]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2619
             in
          uu____2614 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2648 =
            let uu____2653 =
              let uu____2654 =
                let uu____2663 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2663  in
              let uu____2664 =
                let uu____2675 =
                  let uu____2684 =
                    let uu____2685 = e_term_aq aq  in embed uu____2685 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2684  in
                [uu____2675]  in
              uu____2654 :: uu____2664  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2653
             in
          uu____2648 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2713 =
            let uu____2718 =
              let uu____2719 =
                let uu____2728 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2728  in
              [uu____2719]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2718
             in
          uu____2713 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2747 =
            let uu____2752 =
              let uu____2753 =
                let uu____2762 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2762  in
              let uu____2763 =
                let uu____2774 =
                  let uu____2783 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2783  in
                [uu____2774]  in
              uu____2753 :: uu____2763  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2752
             in
          uu____2747 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,attrs,b,t1,t2) ->
          let uu____2823 =
            let uu____2828 =
              let uu____2829 =
                let uu____2838 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2838  in
              let uu____2840 =
                let uu____2851 =
                  let uu____2860 =
                    let uu____2861 = FStar_Syntax_Embeddings.e_list e_term
                       in
                    embed uu____2861 rng attrs  in
                  FStar_Syntax_Syntax.as_arg uu____2860  in
                let uu____2868 =
                  let uu____2879 =
                    let uu____2888 = embed e_bv rng b  in
                    FStar_Syntax_Syntax.as_arg uu____2888  in
                  let uu____2889 =
                    let uu____2900 =
                      let uu____2909 =
                        let uu____2910 = e_term_aq aq  in
                        embed uu____2910 rng t1  in
                      FStar_Syntax_Syntax.as_arg uu____2909  in
                    let uu____2913 =
                      let uu____2924 =
                        let uu____2933 =
                          let uu____2934 = e_term_aq aq  in
                          embed uu____2934 rng t2  in
                        FStar_Syntax_Syntax.as_arg uu____2933  in
                      [uu____2924]  in
                    uu____2900 :: uu____2913  in
                  uu____2879 :: uu____2889  in
                uu____2851 :: uu____2868  in
              uu____2829 :: uu____2840  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2828
             in
          uu____2823 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2991 =
            let uu____2996 =
              let uu____2997 =
                let uu____3006 =
                  let uu____3007 = e_term_aq aq  in embed uu____3007 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____3006  in
              let uu____3010 =
                let uu____3021 =
                  let uu____3030 =
                    let uu____3031 =
                      let uu____3040 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____3040  in
                    embed uu____3031 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____3030  in
                [uu____3021]  in
              uu____2997 :: uu____3010  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2996
             in
          uu____2991 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____3088 =
            let uu____3093 =
              let uu____3094 =
                let uu____3103 =
                  let uu____3104 = e_term_aq aq  in embed uu____3104 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3103  in
              let uu____3107 =
                let uu____3118 =
                  let uu____3127 =
                    let uu____3128 = e_term_aq aq  in embed uu____3128 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____3127  in
                let uu____3131 =
                  let uu____3142 =
                    let uu____3151 =
                      let uu____3152 =
                        let uu____3157 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3157  in
                      embed uu____3152 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3151  in
                  [uu____3142]  in
                uu____3118 :: uu____3131  in
              uu____3094 :: uu____3107  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____3093
             in
          uu____3088 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____3201 =
            let uu____3206 =
              let uu____3207 =
                let uu____3216 =
                  let uu____3217 = e_term_aq aq  in embed uu____3217 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3216  in
              let uu____3220 =
                let uu____3231 =
                  let uu____3240 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____3240  in
                let uu____3241 =
                  let uu____3252 =
                    let uu____3261 =
                      let uu____3262 =
                        let uu____3267 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3267  in
                      embed uu____3262 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3261  in
                  [uu____3252]  in
                uu____3231 :: uu____3241  in
              uu____3207 :: uu____3220  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____3206
             in
          uu____3201 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___387_3304 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___387_3304.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___387_3304.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3322 = FStar_Syntax_Util.head_and_args t  in
      match uu____3322 with
      | (hd1,args) ->
          let uu____3367 =
            let uu____3380 =
              let uu____3381 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3381.FStar_Syntax_Syntax.n  in
            (uu____3380, args)  in
          (match uu____3367 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3396)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3421 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3421
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3428  -> FStar_Pervasives_Native.Some _3428)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3431)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3456 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3456
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3463  -> FStar_Pervasives_Native.Some _3463)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3466)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3491 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3491
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _3498  -> FStar_Pervasives_Native.Some _3498)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3501)::(r,uu____3503)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3538 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3538
                 (fun l1  ->
                    let uu____3544 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3544
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _3551  -> FStar_Pervasives_Native.Some _3551)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3554)::(t1,uu____3556)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3591 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3591
                 (fun b1  ->
                    let uu____3597 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3597
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3604  -> FStar_Pervasives_Native.Some _3604)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3607)::(t1,uu____3609)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3644 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3644
                 (fun b1  ->
                    let uu____3650 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3650
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _3657  -> FStar_Pervasives_Native.Some _3657)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3660)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3685 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3685
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _3692  -> FStar_Pervasives_Native.Some _3692)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3695)::(t1,uu____3697)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3732 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3732
                 (fun b1  ->
                    let uu____3738 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3738
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3745  -> FStar_Pervasives_Native.Some _3745)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3748)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3773 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3773
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _3780  -> FStar_Pervasives_Native.Some _3780)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3783)::(l,uu____3785)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3820 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3820
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _3829  -> FStar_Pervasives_Native.Some _3829)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3832)::(attrs,uu____3834)::(b,uu____3836)::
              (t1,uu____3838)::(t2,uu____3840)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3905 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3905
                 (fun r1  ->
                    let uu____3915 =
                      let uu____3920 = FStar_Syntax_Embeddings.e_list e_term
                         in
                      unembed' w uu____3920 attrs  in
                    FStar_Util.bind_opt uu____3915
                      (fun attrs1  ->
                         let uu____3934 = unembed' w e_bv b  in
                         FStar_Util.bind_opt uu____3934
                           (fun b1  ->
                              let uu____3940 = unembed' w e_term t1  in
                              FStar_Util.bind_opt uu____3940
                                (fun t11  ->
                                   let uu____3946 = unembed' w e_term t2  in
                                   FStar_Util.bind_opt uu____3946
                                     (fun t21  ->
                                        FStar_All.pipe_left
                                          (fun _3953  ->
                                             FStar_Pervasives_Native.Some
                                               _3953)
                                          (FStar_Reflection_Data.Tv_Let
                                             (r1, attrs1, b1, t11, t21)))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3959)::(brs,uu____3961)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3996 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3996
                 (fun t2  ->
                    let uu____4002 =
                      let uu____4007 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____4007 brs  in
                    FStar_Util.bind_opt uu____4002
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _4022  -> FStar_Pervasives_Native.Some _4022)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____4027)::(t1,uu____4029)::(tacopt,uu____4031)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____4076 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4076
                 (fun e1  ->
                    let uu____4082 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____4082
                      (fun t2  ->
                         let uu____4088 =
                           let uu____4093 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4093 tacopt  in
                         FStar_Util.bind_opt uu____4088
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4108  ->
                                   FStar_Pervasives_Native.Some _4108)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____4113)::(c,uu____4115)::(tacopt,uu____4117)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____4162 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4162
                 (fun e1  ->
                    let uu____4168 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____4168
                      (fun c1  ->
                         let uu____4174 =
                           let uu____4179 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4179 tacopt  in
                         FStar_Util.bind_opt uu____4174
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4194  ->
                                   FStar_Pervasives_Native.Some _4194)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _4214  -> FStar_Pervasives_Native.Some _4214)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____4215 ->
               (if w
                then
                  (let uu____4230 =
                     let uu____4236 =
                       let uu____4238 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4238
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4236)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____4230)
                else ();
                FStar_Pervasives_Native.None))
       in
    mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq [] 
let (e_lid : FStar_Ident.lid FStar_Syntax_Embeddings.embedding) =
  let embed1 rng lid =
    let uu____4267 = FStar_Ident.path_of_lid lid  in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____4267  in
  let unembed1 w t =
    let uu____4295 = unembed' w FStar_Syntax_Embeddings.e_string_list t  in
    FStar_Util.map_opt uu____4295
      (fun p  -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos)
     in
  let uu____4312 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x  -> fun r  -> fun uu____4319  -> fun uu____4320  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____4327  -> unembed1 w x) uu____4312
    FStar_Ident.string_of_lid FStar_Syntax_Syntax.ET_abstract
  
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____4344 =
      let uu____4349 =
        let uu____4350 =
          let uu____4359 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____4359  in
        let uu____4361 =
          let uu____4372 =
            let uu____4381 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4381  in
          let uu____4382 =
            let uu____4393 =
              let uu____4402 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4402  in
            [uu____4393]  in
          uu____4372 :: uu____4382  in
        uu____4350 :: uu____4361  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4349
       in
    uu____4344 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4453 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4453 with
    | (hd1,args) ->
        let uu____4498 =
          let uu____4511 =
            let uu____4512 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4512.FStar_Syntax_Syntax.n  in
          (uu____4511, args)  in
        (match uu____4498 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4527)::(idx,uu____4529)::(s,uu____4531)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4576 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4576
               (fun nm1  ->
                  let uu____4586 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4586
                    (fun idx1  ->
                       let uu____4592 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4592
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _4599  ->
                                 FStar_Pervasives_Native.Some _4599)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4600 ->
             (if w
              then
                (let uu____4615 =
                   let uu____4621 =
                     let uu____4623 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4623
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4621)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4615)
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
        let uu____4649 =
          let uu____4654 =
            let uu____4655 =
              let uu____4664 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4664  in
            let uu____4665 =
              let uu____4676 =
                let uu____4685 =
                  let uu____4686 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4686 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4685  in
              [uu____4676]  in
            uu____4655 :: uu____4665  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4654
           in
        uu____4649 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_GTotal (t,md) ->
        let uu____4723 =
          let uu____4728 =
            let uu____4729 =
              let uu____4738 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4738  in
            let uu____4739 =
              let uu____4750 =
                let uu____4759 =
                  let uu____4760 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4760 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4759  in
              [uu____4750]  in
            uu____4729 :: uu____4739  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.t
            uu____4728
           in
        uu____4723 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4796 =
          let uu____4801 =
            let uu____4802 =
              let uu____4811 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4811  in
            let uu____4812 =
              let uu____4823 =
                let uu____4832 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4832  in
              [uu____4823]  in
            uu____4802 :: uu____4812  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4801
           in
        uu____4796 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Eff (us,eff,res,args) ->
        let uu____4869 =
          let uu____4874 =
            let uu____4875 =
              let uu____4884 = embed FStar_Syntax_Embeddings.e_unit rng ()
                 in
              FStar_Syntax_Syntax.as_arg uu____4884  in
            let uu____4885 =
              let uu____4896 =
                let uu____4905 =
                  embed FStar_Syntax_Embeddings.e_string_list rng eff  in
                FStar_Syntax_Syntax.as_arg uu____4905  in
              let uu____4909 =
                let uu____4920 =
                  let uu____4929 = embed e_term rng res  in
                  FStar_Syntax_Syntax.as_arg uu____4929  in
                let uu____4930 =
                  let uu____4941 =
                    let uu____4950 =
                      let uu____4951 = FStar_Syntax_Embeddings.e_list e_argv
                         in
                      embed uu____4951 rng args  in
                    FStar_Syntax_Syntax.as_arg uu____4950  in
                  [uu____4941]  in
                uu____4920 :: uu____4930  in
              uu____4896 :: uu____4909  in
            uu____4875 :: uu____4885  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.t
            uu____4874
           in
        uu____4869 FStar_Pervasives_Native.None rng
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5016 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5016 with
    | (hd1,args) ->
        let uu____5061 =
          let uu____5074 =
            let uu____5075 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5075.FStar_Syntax_Syntax.n  in
          (uu____5074, args)  in
        (match uu____5061 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____5090)::(md,uu____5092)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____5127 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____5127
               (fun t3  ->
                  let uu____5133 =
                    let uu____5138 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____5138 md  in
                  FStar_Util.bind_opt uu____5133
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _5153  -> FStar_Pervasives_Native.Some _5153)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____5158)::(md,uu____5160)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
             ->
             let uu____5195 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____5195
               (fun t3  ->
                  let uu____5201 =
                    let uu____5206 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____5206 md  in
                  FStar_Util.bind_opt uu____5201
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _5221  -> FStar_Pervasives_Native.Some _5221)
                         (FStar_Reflection_Data.C_GTotal (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____5226)::(post,uu____5228)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____5263 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____5263
               (fun pre1  ->
                  let uu____5269 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____5269
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _5276  -> FStar_Pervasives_Native.Some _5276)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(us,uu____5279)::(eff,uu____5281)::(res,uu____5283)::(args1,uu____5285)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
             ->
             let uu____5340 = unembed' w FStar_Syntax_Embeddings.e_unit us
                in
             FStar_Util.bind_opt uu____5340
               (fun us1  ->
                  let uu____5346 =
                    unembed' w FStar_Syntax_Embeddings.e_string_list eff  in
                  FStar_Util.bind_opt uu____5346
                    (fun eff1  ->
                       let uu____5364 = unembed' w e_term res  in
                       FStar_Util.bind_opt uu____5364
                         (fun res1  ->
                            let uu____5370 =
                              let uu____5375 =
                                FStar_Syntax_Embeddings.e_list e_argv  in
                              unembed' w uu____5375 args1  in
                            FStar_Util.bind_opt uu____5370
                              (fun args2  ->
                                 FStar_All.pipe_left
                                   (fun _5390  ->
                                      FStar_Pervasives_Native.Some _5390)
                                   (FStar_Reflection_Data.C_Eff
                                      ([], eff1, res1, args2))))))
         | uu____5395 ->
             (if w
              then
                (let uu____5410 =
                   let uu____5416 =
                     let uu____5418 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____5418
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5416)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5410)
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
    let uu___708_5443 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___708_5443.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___708_5443.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5464 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5464 with
    | (hd1,args) ->
        let uu____5509 =
          let uu____5524 =
            let uu____5525 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5525.FStar_Syntax_Syntax.n  in
          (uu____5524, args)  in
        (match uu____5509 with
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
         | uu____5597 ->
             (if w
              then
                (let uu____5614 =
                   let uu____5620 =
                     let uu____5622 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____5622
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5620)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5614)
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
    let uu____5659 =
      let uu____5660 = FStar_Syntax_Subst.compress t  in
      uu____5660.FStar_Syntax_Syntax.n  in
    match uu____5659 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5666;
          FStar_Syntax_Syntax.rng = uu____5667;_}
        ->
        let uu____5670 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5670
    | uu____5671 ->
        (if w
         then
           (let uu____5674 =
              let uu____5680 =
                let uu____5682 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5682
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5680)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5674)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____5722 uu____5723 =
    let uu____5725 =
      let uu____5731 = FStar_Ident.range_of_id i  in
      let uu____5732 = FStar_Ident.text_of_id i  in (uu____5731, uu____5732)
       in
    embed repr rng uu____5725  in
  let unembed_ident t w uu____5759 =
    let uu____5764 = unembed' w repr t  in
    match uu____5764 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5788 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5788
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5795 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5795
  
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
        let uu____5834 =
          let uu____5839 =
            let uu____5840 =
              let uu____5849 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5849  in
            let uu____5851 =
              let uu____5862 =
                let uu____5871 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5871  in
              let uu____5872 =
                let uu____5883 =
                  let uu____5892 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5892  in
                let uu____5895 =
                  let uu____5906 =
                    let uu____5915 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5915  in
                  let uu____5916 =
                    let uu____5927 =
                      let uu____5936 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5936  in
                    [uu____5927]  in
                  uu____5906 :: uu____5916  in
                uu____5883 :: uu____5895  in
              uu____5862 :: uu____5872  in
            uu____5840 :: uu____5851  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5839
           in
        uu____5834 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5987 =
          let uu____5992 =
            let uu____5993 =
              let uu____6002 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____6002  in
            let uu____6006 =
              let uu____6017 =
                let uu____6026 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____6026  in
              [uu____6017]  in
            uu____5993 :: uu____6006  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5992
           in
        uu____5987 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____6068 =
          let uu____6073 =
            let uu____6074 =
              let uu____6083 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____6083  in
            let uu____6087 =
              let uu____6098 =
                let uu____6107 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____6107  in
              let uu____6110 =
                let uu____6121 =
                  let uu____6130 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____6130  in
                let uu____6131 =
                  let uu____6142 =
                    let uu____6151 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____6151  in
                  let uu____6152 =
                    let uu____6163 =
                      let uu____6172 =
                        let uu____6173 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____6173 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____6172  in
                    [uu____6163]  in
                  uu____6142 :: uu____6152  in
                uu____6121 :: uu____6131  in
              uu____6098 :: uu____6110  in
            uu____6074 :: uu____6087  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____6073
           in
        uu____6068 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___784_6237 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___784_6237.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___784_6237.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6256 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6256 with
    | (hd1,args) ->
        let uu____6301 =
          let uu____6314 =
            let uu____6315 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6315.FStar_Syntax_Syntax.n  in
          (uu____6314, args)  in
        (match uu____6301 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____6330)::(us,uu____6332)::(bs,uu____6334)::(t2,uu____6336)::
            (dcs,uu____6338)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____6403 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____6403
               (fun nm1  ->
                  let uu____6421 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____6421
                    (fun us1  ->
                       let uu____6435 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____6435
                         (fun bs1  ->
                            let uu____6441 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____6441
                              (fun t3  ->
                                 let uu____6447 =
                                   let uu____6455 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____6455 dcs  in
                                 FStar_Util.bind_opt uu____6447
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _6485  ->
                                           FStar_Pervasives_Native.Some _6485)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____6494)::(fvar1,uu____6496)::(univs1,uu____6498)::
            (ty,uu____6500)::(t2,uu____6502)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____6567 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____6567
               (fun r1  ->
                  let uu____6577 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____6577
                    (fun fvar2  ->
                       let uu____6583 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____6583
                         (fun univs2  ->
                            let uu____6597 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____6597
                              (fun ty1  ->
                                 let uu____6603 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____6603
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _6610  ->
                                           FStar_Pervasives_Native.Some _6610)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6629 ->
             (if w
              then
                (let uu____6644 =
                   let uu____6650 =
                     let uu____6652 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6652
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6650)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6644)
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
          let uu____6678 =
            let uu____6683 =
              let uu____6684 =
                let uu____6693 =
                  let uu____6694 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6694  in
                FStar_Syntax_Syntax.as_arg uu____6693  in
              [uu____6684]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6683
             in
          uu____6678 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6714 =
            let uu____6719 =
              let uu____6720 =
                let uu____6729 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6729  in
              let uu____6730 =
                let uu____6741 =
                  let uu____6750 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6750  in
                [uu____6741]  in
              uu____6720 :: uu____6730  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6719
             in
          uu____6714 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___859_6775 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___859_6775.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___859_6775.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6796 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6796 with
    | (hd1,args) ->
        let uu____6841 =
          let uu____6854 =
            let uu____6855 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6855.FStar_Syntax_Syntax.n  in
          (uu____6854, args)  in
        (match uu____6841 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6885)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6910 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6910
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _6917  -> FStar_Pervasives_Native.Some _6917)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6920)::(e2,uu____6922)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6957 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6957
               (fun e11  ->
                  let uu____6963 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6963
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _6970  -> FStar_Pervasives_Native.Some _6970)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6971 ->
             (if w
              then
                (let uu____6986 =
                   let uu____6992 =
                     let uu____6994 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6994
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6992)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6986)
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
let (e_qualifier :
  FStar_Reflection_Data.qualifier FStar_Syntax_Embeddings.embedding) =
  let embed1 rng q =
    let r =
      match q with
      | FStar_Reflection_Data.Assumption  ->
          FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.t
      | FStar_Reflection_Data.New  ->
          FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Private  ->
          FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Unfold_for_unification_and_vcgen  ->
          FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Visible_default  ->
          FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Irreducible  ->
          FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Abstract  ->
          FStar_Reflection_Data.ref_qual_Abstract.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Inline_for_extraction  ->
          FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.t
      | FStar_Reflection_Data.NoExtract  ->
          FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Noeq  ->
          FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Unopteq  ->
          FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.t
      | FStar_Reflection_Data.TotalEffect  ->
          FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Logic  ->
          FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Reifiable  ->
          FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.t
      | FStar_Reflection_Data.ExceptionConstructor  ->
          FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.t
      | FStar_Reflection_Data.HasMaskedEffect  ->
          FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Effect  ->
          FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.t
      | FStar_Reflection_Data.OnlyName  ->
          FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Reflectable l ->
          let uu____7031 =
            let uu____7036 =
              let uu____7037 =
                let uu____7046 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7046  in
              [uu____7037]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
              uu____7036
             in
          uu____7031 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu____7064 =
            let uu____7069 =
              let uu____7070 =
                let uu____7079 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7079  in
              [uu____7070]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
              uu____7069
             in
          uu____7064 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu____7097 =
            let uu____7102 =
              let uu____7103 =
                let uu____7112 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7112  in
              [uu____7103]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
              uu____7102
             in
          uu____7097 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Projector (l,i) ->
          let uu____7131 =
            let uu____7136 =
              let uu____7137 =
                let uu____7146 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7146  in
              let uu____7147 =
                let uu____7158 =
                  let uu____7167 = embed e_ident rng i  in
                  FStar_Syntax_Syntax.as_arg uu____7167  in
                [uu____7158]  in
              uu____7137 :: uu____7147  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
              uu____7136
             in
          uu____7131 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordType (ids1,ids2) ->
          let uu____7202 =
            let uu____7207 =
              let uu____7208 =
                let uu____7217 =
                  let uu____7218 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7218 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____7217  in
              let uu____7225 =
                let uu____7236 =
                  let uu____7245 =
                    let uu____7246 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____7246 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____7245  in
                [uu____7236]  in
              uu____7208 :: uu____7225  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
              uu____7207
             in
          uu____7202 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1,ids2) ->
          let uu____7287 =
            let uu____7292 =
              let uu____7293 =
                let uu____7302 =
                  let uu____7303 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7303 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____7302  in
              let uu____7310 =
                let uu____7321 =
                  let uu____7330 =
                    let uu____7331 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____7331 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____7330  in
                [uu____7321]  in
              uu____7293 :: uu____7310  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
              uu____7292
             in
          uu____7287 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___935_7362 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___935_7362.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___935_7362.FStar_Syntax_Syntax.vars)
    }  in
  let unembed1 w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____7383 = FStar_Syntax_Util.head_and_args t1  in
    match uu____7383 with
    | (hd1,args) ->
        let uu____7428 =
          let uu____7441 =
            let uu____7442 = FStar_Syntax_Util.un_uinst hd1  in
            uu____7442.FStar_Syntax_Syntax.n  in
          (uu____7441, args)  in
        (match uu____7428 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Assumption.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Assumption
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_New.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.New
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Private.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Private
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.Unfold_for_unification_and_vcgen
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Visible_default.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.Visible_default
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Irreducible.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_Data.Irreducible
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Abstract.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Abstract
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Inline_for_extraction.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.Inline_for_extraction
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_NoExtract.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.NoExtract
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Noeq.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Noeq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Unopteq.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unopteq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_TotalEffect.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_Data.TotalEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Logic.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Logic
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reifiable.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Reifiable
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_ExceptionConstructor.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.ExceptionConstructor
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_HasMaskedEffect.FStar_Reflection_Data.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_Data.HasMaskedEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Effect.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Effect
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_OnlyName.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.OnlyName
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7727)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7752 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7752
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7759  -> FStar_Pervasives_Native.Some _7759)
                    (FStar_Reflection_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7762)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7787 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7787
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7794  -> FStar_Pervasives_Native.Some _7794)
                    (FStar_Reflection_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7797)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7822 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7822
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7829  -> FStar_Pervasives_Native.Some _7829)
                    (FStar_Reflection_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7832)::(i,uu____7834)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7869 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7869
               (fun l1  ->
                  let uu____7875 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7875
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun _7882  -> FStar_Pervasives_Native.Some _7882)
                         (FStar_Reflection_Data.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7885)::(ids2,uu____7887)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7922 =
               let uu____7927 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7927 ids1  in
             FStar_Util.bind_opt uu____7922
               (fun ids11  ->
                  let uu____7941 =
                    let uu____7946 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7946 ids2  in
                  FStar_Util.bind_opt uu____7941
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7961  -> FStar_Pervasives_Native.Some _7961)
                         (FStar_Reflection_Data.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7968)::(ids2,uu____7970)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____8005 =
               let uu____8010 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____8010 ids1  in
             FStar_Util.bind_opt uu____8005
               (fun ids11  ->
                  let uu____8024 =
                    let uu____8029 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____8029 ids2  in
                  FStar_Util.bind_opt uu____8024
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _8044  -> FStar_Pervasives_Native.Some _8044)
                         (FStar_Reflection_Data.RecordConstructor
                            (ids11, ids21))))
         | uu____8049 ->
             (if w
              then
                (let uu____8064 =
                   let uu____8070 =
                     let uu____8072 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____8072
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____8070)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____8064)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed1 unembed1 FStar_Reflection_Data.fstar_refl_qualifier 
let (e_qualifiers :
  FStar_Reflection_Data.qualifier Prims.list
    FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_qualifier 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8090 =
      let uu____8095 =
        let uu____8096 =
          let uu____8105 =
            let uu____8106 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____8106  in
          FStar_Syntax_Syntax.as_arg uu____8105  in
        [uu____8096]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____8095
       in
    uu____8090 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8130 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____8130 with
    | (bv,aq) ->
        let uu____8137 =
          let uu____8142 =
            let uu____8143 =
              let uu____8152 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____8152  in
            let uu____8153 =
              let uu____8164 =
                let uu____8173 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____8173  in
              [uu____8164]  in
            uu____8143 :: uu____8153  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____8142
           in
        uu____8137 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8205 =
      let uu____8210 =
        let uu____8211 =
          let uu____8220 =
            let uu____8221 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____8228 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____8221 i.FStar_Syntax_Syntax.rng uu____8228  in
          FStar_Syntax_Syntax.as_arg uu____8220  in
        [uu____8211]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____8210
       in
    uu____8205 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8258 =
      let uu____8263 =
        let uu____8264 =
          let uu____8273 =
            let uu____8274 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____8274  in
          FStar_Syntax_Syntax.as_arg uu____8273  in
        [uu____8264]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____8263
       in
    uu____8258 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
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
    let uu____8310 =
      let uu____8315 =
        let uu____8316 =
          let uu____8325 =
            let uu____8326 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____8326  in
          FStar_Syntax_Syntax.as_arg uu____8325  in
        [uu____8316]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____8315
       in
    uu____8310 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  