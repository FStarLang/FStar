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
let (e_branch_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2266 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2266
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2281 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2281 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2304 =
            let uu____2309 =
              let uu____2310 =
                let uu____2319 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2319  in
              [uu____2310]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____2309
             in
          uu____2304 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2337 =
            let uu____2342 =
              let uu____2343 =
                let uu____2352 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2352  in
              [uu____2343]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2342
             in
          uu____2337 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2370 =
            let uu____2375 =
              let uu____2376 =
                let uu____2385 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2385  in
              [uu____2376]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2375
             in
          uu____2370 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2404 =
            let uu____2409 =
              let uu____2410 =
                let uu____2419 =
                  let uu____2420 = e_term_aq aq  in embed uu____2420 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2419  in
              let uu____2423 =
                let uu____2434 =
                  let uu____2443 =
                    let uu____2444 = e_argv_aq aq  in embed uu____2444 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2443  in
                [uu____2434]  in
              uu____2410 :: uu____2423  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2409
             in
          uu____2404 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2481 =
            let uu____2486 =
              let uu____2487 =
                let uu____2496 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2496  in
              let uu____2497 =
                let uu____2508 =
                  let uu____2517 =
                    let uu____2518 = e_term_aq aq  in embed uu____2518 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2517  in
                [uu____2508]  in
              uu____2487 :: uu____2497  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2486
             in
          uu____2481 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2547 =
            let uu____2552 =
              let uu____2553 =
                let uu____2562 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2562  in
              let uu____2563 =
                let uu____2574 =
                  let uu____2583 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2583  in
                [uu____2574]  in
              uu____2553 :: uu____2563  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2552
             in
          uu____2547 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2609 =
            let uu____2614 =
              let uu____2615 =
                let uu____2624 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2624  in
              [uu____2615]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2614
             in
          uu____2609 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2643 =
            let uu____2648 =
              let uu____2649 =
                let uu____2658 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2658  in
              let uu____2659 =
                let uu____2670 =
                  let uu____2679 =
                    let uu____2680 = e_term_aq aq  in embed uu____2680 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2679  in
                [uu____2670]  in
              uu____2649 :: uu____2659  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2648
             in
          uu____2643 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2708 =
            let uu____2713 =
              let uu____2714 =
                let uu____2723 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2723  in
              [uu____2714]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2713
             in
          uu____2708 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2742 =
            let uu____2747 =
              let uu____2748 =
                let uu____2757 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2757  in
              let uu____2758 =
                let uu____2769 =
                  let uu____2778 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2778  in
                [uu____2769]  in
              uu____2748 :: uu____2758  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2747
             in
          uu____2742 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,attrs,b,t1,t2) ->
          let uu____2818 =
            let uu____2823 =
              let uu____2824 =
                let uu____2833 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2833  in
              let uu____2835 =
                let uu____2846 =
                  let uu____2855 =
                    let uu____2856 = FStar_Syntax_Embeddings.e_list e_term
                       in
                    embed uu____2856 rng attrs  in
                  FStar_Syntax_Syntax.as_arg uu____2855  in
                let uu____2863 =
                  let uu____2874 =
                    let uu____2883 = embed e_bv rng b  in
                    FStar_Syntax_Syntax.as_arg uu____2883  in
                  let uu____2884 =
                    let uu____2895 =
                      let uu____2904 =
                        let uu____2905 = e_term_aq aq  in
                        embed uu____2905 rng t1  in
                      FStar_Syntax_Syntax.as_arg uu____2904  in
                    let uu____2908 =
                      let uu____2919 =
                        let uu____2928 =
                          let uu____2929 = e_term_aq aq  in
                          embed uu____2929 rng t2  in
                        FStar_Syntax_Syntax.as_arg uu____2928  in
                      [uu____2919]  in
                    uu____2895 :: uu____2908  in
                  uu____2874 :: uu____2884  in
                uu____2846 :: uu____2863  in
              uu____2824 :: uu____2835  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2823
             in
          uu____2818 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2986 =
            let uu____2991 =
              let uu____2992 =
                let uu____3001 =
                  let uu____3002 = e_term_aq aq  in embed uu____3002 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____3001  in
              let uu____3005 =
                let uu____3016 =
                  let uu____3025 =
                    let uu____3026 =
                      let uu____3035 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____3035  in
                    embed uu____3026 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____3025  in
                [uu____3016]  in
              uu____2992 :: uu____3005  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2991
             in
          uu____2986 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____3083 =
            let uu____3088 =
              let uu____3089 =
                let uu____3098 =
                  let uu____3099 = e_term_aq aq  in embed uu____3099 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3098  in
              let uu____3102 =
                let uu____3113 =
                  let uu____3122 =
                    let uu____3123 = e_term_aq aq  in embed uu____3123 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____3122  in
                let uu____3126 =
                  let uu____3137 =
                    let uu____3146 =
                      let uu____3147 =
                        let uu____3152 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3152  in
                      embed uu____3147 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3146  in
                  [uu____3137]  in
                uu____3113 :: uu____3126  in
              uu____3089 :: uu____3102  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____3088
             in
          uu____3083 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____3196 =
            let uu____3201 =
              let uu____3202 =
                let uu____3211 =
                  let uu____3212 = e_term_aq aq  in embed uu____3212 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3211  in
              let uu____3215 =
                let uu____3226 =
                  let uu____3235 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____3235  in
                let uu____3236 =
                  let uu____3247 =
                    let uu____3256 =
                      let uu____3257 =
                        let uu____3262 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3262  in
                      embed uu____3257 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3256  in
                  [uu____3247]  in
                uu____3226 :: uu____3236  in
              uu____3202 :: uu____3215  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____3201
             in
          uu____3196 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___387_3299 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___387_3299.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___387_3299.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3317 = FStar_Syntax_Util.head_and_args t  in
      match uu____3317 with
      | (hd1,args) ->
          let uu____3362 =
            let uu____3375 =
              let uu____3376 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3376.FStar_Syntax_Syntax.n  in
            (uu____3375, args)  in
          (match uu____3362 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3391)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3416 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3416
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3423  -> FStar_Pervasives_Native.Some _3423)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3426)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3451 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3451
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3458  -> FStar_Pervasives_Native.Some _3458)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3461)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3486 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3486
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _3493  -> FStar_Pervasives_Native.Some _3493)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3496)::(r,uu____3498)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3533 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3533
                 (fun l1  ->
                    let uu____3539 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3539
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _3546  -> FStar_Pervasives_Native.Some _3546)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3549)::(t1,uu____3551)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3586 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3586
                 (fun b1  ->
                    let uu____3592 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3592
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3599  -> FStar_Pervasives_Native.Some _3599)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3602)::(t1,uu____3604)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3639 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3639
                 (fun b1  ->
                    let uu____3645 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3645
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _3652  -> FStar_Pervasives_Native.Some _3652)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3655)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3680 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3680
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _3687  -> FStar_Pervasives_Native.Some _3687)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3690)::(t1,uu____3692)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3727 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3727
                 (fun b1  ->
                    let uu____3733 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3733
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3740  -> FStar_Pervasives_Native.Some _3740)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3743)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3768 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3768
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _3775  -> FStar_Pervasives_Native.Some _3775)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3778)::(l,uu____3780)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3815 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3815
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _3824  -> FStar_Pervasives_Native.Some _3824)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3827)::(attrs,uu____3829)::(b,uu____3831)::
              (t1,uu____3833)::(t2,uu____3835)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3900 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3900
                 (fun r1  ->
                    let uu____3910 =
                      let uu____3915 = FStar_Syntax_Embeddings.e_list e_term
                         in
                      unembed' w uu____3915 attrs  in
                    FStar_Util.bind_opt uu____3910
                      (fun attrs1  ->
                         let uu____3929 = unembed' w e_bv b  in
                         FStar_Util.bind_opt uu____3929
                           (fun b1  ->
                              let uu____3935 = unembed' w e_term t1  in
                              FStar_Util.bind_opt uu____3935
                                (fun t11  ->
                                   let uu____3941 = unembed' w e_term t2  in
                                   FStar_Util.bind_opt uu____3941
                                     (fun t21  ->
                                        FStar_All.pipe_left
                                          (fun _3948  ->
                                             FStar_Pervasives_Native.Some
                                               _3948)
                                          (FStar_Reflection_Data.Tv_Let
                                             (r1, attrs1, b1, t11, t21)))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3954)::(brs,uu____3956)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3991 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3991
                 (fun t2  ->
                    let uu____3997 =
                      let uu____4002 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____4002 brs  in
                    FStar_Util.bind_opt uu____3997
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _4017  -> FStar_Pervasives_Native.Some _4017)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____4022)::(t1,uu____4024)::(tacopt,uu____4026)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____4071 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4071
                 (fun e1  ->
                    let uu____4077 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____4077
                      (fun t2  ->
                         let uu____4083 =
                           let uu____4088 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4088 tacopt  in
                         FStar_Util.bind_opt uu____4083
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4103  ->
                                   FStar_Pervasives_Native.Some _4103)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____4108)::(c,uu____4110)::(tacopt,uu____4112)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____4157 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4157
                 (fun e1  ->
                    let uu____4163 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____4163
                      (fun c1  ->
                         let uu____4169 =
                           let uu____4174 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4174 tacopt  in
                         FStar_Util.bind_opt uu____4169
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4189  ->
                                   FStar_Pervasives_Native.Some _4189)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _4209  -> FStar_Pervasives_Native.Some _4209)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____4210 ->
               (if w
                then
                  (let uu____4225 =
                     let uu____4231 =
                       let uu____4233 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4233
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4231)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____4225)
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
    let uu____4262 =
      let uu____4267 =
        let uu____4268 =
          let uu____4277 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____4277  in
        let uu____4279 =
          let uu____4290 =
            let uu____4299 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4299  in
          let uu____4300 =
            let uu____4311 =
              let uu____4320 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4320  in
            [uu____4311]  in
          uu____4290 :: uu____4300  in
        uu____4268 :: uu____4279  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4267
       in
    uu____4262 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4371 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4371 with
    | (hd1,args) ->
        let uu____4416 =
          let uu____4429 =
            let uu____4430 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4430.FStar_Syntax_Syntax.n  in
          (uu____4429, args)  in
        (match uu____4416 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4445)::(idx,uu____4447)::(s,uu____4449)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4494 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4494
               (fun nm1  ->
                  let uu____4504 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4504
                    (fun idx1  ->
                       let uu____4510 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4510
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _4517  ->
                                 FStar_Pervasives_Native.Some _4517)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4518 ->
             (if w
              then
                (let uu____4533 =
                   let uu____4539 =
                     let uu____4541 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4541
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4539)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4533)
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
        let uu____4567 =
          let uu____4572 =
            let uu____4573 =
              let uu____4582 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4582  in
            let uu____4583 =
              let uu____4594 =
                let uu____4603 =
                  let uu____4604 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4604 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4603  in
              [uu____4594]  in
            uu____4573 :: uu____4583  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4572
           in
        uu____4567 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4640 =
          let uu____4645 =
            let uu____4646 =
              let uu____4655 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4655  in
            let uu____4656 =
              let uu____4667 =
                let uu____4676 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4676  in
              [uu____4667]  in
            uu____4646 :: uu____4656  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4645
           in
        uu____4640 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___612_4701 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___612_4701.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___612_4701.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4720 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4720 with
    | (hd1,args) ->
        let uu____4765 =
          let uu____4778 =
            let uu____4779 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4779.FStar_Syntax_Syntax.n  in
          (uu____4778, args)  in
        (match uu____4765 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4794)::(md,uu____4796)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4831 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4831
               (fun t3  ->
                  let uu____4837 =
                    let uu____4842 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4842 md  in
                  FStar_Util.bind_opt uu____4837
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _4857  -> FStar_Pervasives_Native.Some _4857)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4862)::(post,uu____4864)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4899 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4899
               (fun pre1  ->
                  let uu____4905 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4905
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _4912  -> FStar_Pervasives_Native.Some _4912)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _4930  -> FStar_Pervasives_Native.Some _4930)
               FStar_Reflection_Data.C_Unknown
         | uu____4931 ->
             (if w
              then
                (let uu____4946 =
                   let uu____4952 =
                     let uu____4954 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4954
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4952)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4946)
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
    let uu___659_4979 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___659_4979.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___659_4979.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5000 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5000 with
    | (hd1,args) ->
        let uu____5045 =
          let uu____5060 =
            let uu____5061 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5061.FStar_Syntax_Syntax.n  in
          (uu____5060, args)  in
        (match uu____5045 with
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
         | uu____5133 ->
             (if w
              then
                (let uu____5150 =
                   let uu____5156 =
                     let uu____5158 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____5158
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5156)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5150)
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
    let uu____5195 =
      let uu____5196 = FStar_Syntax_Subst.compress t  in
      uu____5196.FStar_Syntax_Syntax.n  in
    match uu____5195 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5202;
          FStar_Syntax_Syntax.rng = uu____5203;_}
        ->
        let uu____5206 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5206
    | uu____5207 ->
        (if w
         then
           (let uu____5210 =
              let uu____5216 =
                let uu____5218 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5218
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5216)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5210)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____5258 uu____5259 =
    let uu____5261 =
      let uu____5267 = FStar_Ident.range_of_id i  in
      let uu____5268 = FStar_Ident.text_of_id i  in (uu____5267, uu____5268)
       in
    embed repr rng uu____5261  in
  let unembed_ident t w uu____5295 =
    let uu____5300 = unembed' w repr t  in
    match uu____5300 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5324 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5324
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5331 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5331
  
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
        let uu____5370 =
          let uu____5375 =
            let uu____5376 =
              let uu____5385 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5385  in
            let uu____5387 =
              let uu____5398 =
                let uu____5407 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5407  in
              let uu____5408 =
                let uu____5419 =
                  let uu____5428 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5428  in
                let uu____5431 =
                  let uu____5442 =
                    let uu____5451 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5451  in
                  let uu____5452 =
                    let uu____5463 =
                      let uu____5472 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5472  in
                    [uu____5463]  in
                  uu____5442 :: uu____5452  in
                uu____5419 :: uu____5431  in
              uu____5398 :: uu____5408  in
            uu____5376 :: uu____5387  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5375
           in
        uu____5370 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5523 =
          let uu____5528 =
            let uu____5529 =
              let uu____5538 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5538  in
            let uu____5542 =
              let uu____5553 =
                let uu____5562 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5562  in
              [uu____5553]  in
            uu____5529 :: uu____5542  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5528
           in
        uu____5523 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5604 =
          let uu____5609 =
            let uu____5610 =
              let uu____5619 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5619  in
            let uu____5623 =
              let uu____5634 =
                let uu____5643 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5643  in
              let uu____5646 =
                let uu____5657 =
                  let uu____5666 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5666  in
                let uu____5667 =
                  let uu____5678 =
                    let uu____5687 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5687  in
                  let uu____5688 =
                    let uu____5699 =
                      let uu____5708 =
                        let uu____5709 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5709 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5708  in
                    [uu____5699]  in
                  uu____5678 :: uu____5688  in
                uu____5657 :: uu____5667  in
              uu____5634 :: uu____5646  in
            uu____5610 :: uu____5623  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5609
           in
        uu____5604 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___735_5773 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___735_5773.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___735_5773.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5792 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5792 with
    | (hd1,args) ->
        let uu____5837 =
          let uu____5850 =
            let uu____5851 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5851.FStar_Syntax_Syntax.n  in
          (uu____5850, args)  in
        (match uu____5837 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5866)::(us,uu____5868)::(bs,uu____5870)::(t2,uu____5872)::
            (dcs,uu____5874)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5939 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5939
               (fun nm1  ->
                  let uu____5957 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5957
                    (fun us1  ->
                       let uu____5971 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5971
                         (fun bs1  ->
                            let uu____5977 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5977
                              (fun t3  ->
                                 let uu____5983 =
                                   let uu____5991 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5991 dcs  in
                                 FStar_Util.bind_opt uu____5983
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _6021  ->
                                           FStar_Pervasives_Native.Some _6021)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____6030)::(fvar1,uu____6032)::(univs1,uu____6034)::
            (ty,uu____6036)::(t2,uu____6038)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____6103 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____6103
               (fun r1  ->
                  let uu____6113 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____6113
                    (fun fvar2  ->
                       let uu____6119 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____6119
                         (fun univs2  ->
                            let uu____6133 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____6133
                              (fun ty1  ->
                                 let uu____6139 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____6139
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _6146  ->
                                           FStar_Pervasives_Native.Some _6146)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6165 ->
             (if w
              then
                (let uu____6180 =
                   let uu____6186 =
                     let uu____6188 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6188
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6186)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6180)
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
          let uu____6214 =
            let uu____6219 =
              let uu____6220 =
                let uu____6229 =
                  let uu____6230 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6230  in
                FStar_Syntax_Syntax.as_arg uu____6229  in
              [uu____6220]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6219
             in
          uu____6214 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6250 =
            let uu____6255 =
              let uu____6256 =
                let uu____6265 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6265  in
              let uu____6266 =
                let uu____6277 =
                  let uu____6286 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6286  in
                [uu____6277]  in
              uu____6256 :: uu____6266  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6255
             in
          uu____6250 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___810_6311 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___810_6311.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___810_6311.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6332 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6332 with
    | (hd1,args) ->
        let uu____6377 =
          let uu____6390 =
            let uu____6391 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6391.FStar_Syntax_Syntax.n  in
          (uu____6390, args)  in
        (match uu____6377 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6421)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6446 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6446
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _6453  -> FStar_Pervasives_Native.Some _6453)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6456)::(e2,uu____6458)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6493 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6493
               (fun e11  ->
                  let uu____6499 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6499
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _6506  -> FStar_Pervasives_Native.Some _6506)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6507 ->
             (if w
              then
                (let uu____6522 =
                   let uu____6528 =
                     let uu____6530 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6530
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6528)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6522)
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
    let uu____6561 = FStar_Ident.path_of_lid lid  in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____6561  in
  let unembed1 w t =
    let uu____6589 = unembed' w FStar_Syntax_Embeddings.e_string_list t  in
    FStar_Util.map_opt uu____6589
      (fun p  -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos)
     in
  let uu____6606 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x  -> fun r  -> fun uu____6613  -> fun uu____6614  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____6621  -> unembed1 w x) uu____6606
    FStar_Ident.string_of_lid FStar_Syntax_Syntax.ET_abstract
  
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
          let uu____6644 =
            let uu____6649 =
              let uu____6650 =
                let uu____6659 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6659  in
              [uu____6650]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
              uu____6649
             in
          uu____6644 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu____6677 =
            let uu____6682 =
              let uu____6683 =
                let uu____6692 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6692  in
              [uu____6683]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
              uu____6682
             in
          uu____6677 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu____6710 =
            let uu____6715 =
              let uu____6716 =
                let uu____6725 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6725  in
              [uu____6716]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
              uu____6715
             in
          uu____6710 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Projector (l,i) ->
          let uu____6744 =
            let uu____6749 =
              let uu____6750 =
                let uu____6759 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____6759  in
              let uu____6760 =
                let uu____6771 =
                  let uu____6780 = embed e_ident rng i  in
                  FStar_Syntax_Syntax.as_arg uu____6780  in
                [uu____6771]  in
              uu____6750 :: uu____6760  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
              uu____6749
             in
          uu____6744 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordType (ids1,ids2) ->
          let uu____6815 =
            let uu____6820 =
              let uu____6821 =
                let uu____6830 =
                  let uu____6831 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6831 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6830  in
              let uu____6838 =
                let uu____6849 =
                  let uu____6858 =
                    let uu____6859 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6859 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6858  in
                [uu____6849]  in
              uu____6821 :: uu____6838  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
              uu____6820
             in
          uu____6815 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1,ids2) ->
          let uu____6900 =
            let uu____6905 =
              let uu____6906 =
                let uu____6915 =
                  let uu____6916 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____6916 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____6915  in
              let uu____6923 =
                let uu____6934 =
                  let uu____6943 =
                    let uu____6944 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____6944 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____6943  in
                [uu____6934]  in
              uu____6906 :: uu____6923  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
              uu____6905
             in
          uu____6900 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___900_6975 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___900_6975.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___900_6975.FStar_Syntax_Syntax.vars)
    }  in
  let unembed1 w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6996 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6996 with
    | (hd1,args) ->
        let uu____7041 =
          let uu____7054 =
            let uu____7055 = FStar_Syntax_Util.un_uinst hd1  in
            uu____7055.FStar_Syntax_Syntax.n  in
          (uu____7054, args)  in
        (match uu____7041 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7340)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7365 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7365
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7372  -> FStar_Pervasives_Native.Some _7372)
                    (FStar_Reflection_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7375)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7400 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7400
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7407  -> FStar_Pervasives_Native.Some _7407)
                    (FStar_Reflection_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7410)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7435 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7435
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7442  -> FStar_Pervasives_Native.Some _7442)
                    (FStar_Reflection_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7445)::(i,uu____7447)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7482 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7482
               (fun l1  ->
                  let uu____7488 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7488
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun _7495  -> FStar_Pervasives_Native.Some _7495)
                         (FStar_Reflection_Data.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7498)::(ids2,uu____7500)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7535 =
               let uu____7540 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7540 ids1  in
             FStar_Util.bind_opt uu____7535
               (fun ids11  ->
                  let uu____7554 =
                    let uu____7559 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7559 ids2  in
                  FStar_Util.bind_opt uu____7554
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7574  -> FStar_Pervasives_Native.Some _7574)
                         (FStar_Reflection_Data.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7581)::(ids2,uu____7583)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____7618 =
               let uu____7623 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7623 ids1  in
             FStar_Util.bind_opt uu____7618
               (fun ids11  ->
                  let uu____7637 =
                    let uu____7642 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7642 ids2  in
                  FStar_Util.bind_opt uu____7637
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _7657  -> FStar_Pervasives_Native.Some _7657)
                         (FStar_Reflection_Data.RecordConstructor
                            (ids11, ids21))))
         | uu____7662 ->
             (if w
              then
                (let uu____7677 =
                   let uu____7683 =
                     let uu____7685 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____7685
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____7683)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7677)
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
    let uu____7703 =
      let uu____7708 =
        let uu____7709 =
          let uu____7718 =
            let uu____7719 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____7719  in
          FStar_Syntax_Syntax.as_arg uu____7718  in
        [uu____7709]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____7708
       in
    uu____7703 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7743 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____7743 with
    | (bv,aq) ->
        let uu____7750 =
          let uu____7755 =
            let uu____7756 =
              let uu____7765 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____7765  in
            let uu____7766 =
              let uu____7777 =
                let uu____7786 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____7786  in
              [uu____7777]  in
            uu____7756 :: uu____7766  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____7755
           in
        uu____7750 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7818 =
      let uu____7823 =
        let uu____7824 =
          let uu____7833 =
            let uu____7834 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____7841 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____7834 i.FStar_Syntax_Syntax.rng uu____7841  in
          FStar_Syntax_Syntax.as_arg uu____7833  in
        [uu____7824]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____7823
       in
    uu____7818 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7871 =
      let uu____7876 =
        let uu____7877 =
          let uu____7886 =
            let uu____7887 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____7887  in
          FStar_Syntax_Syntax.as_arg uu____7886  in
        [uu____7877]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____7876
       in
    uu____7871 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
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
    let uu____7923 =
      let uu____7928 =
        let uu____7929 =
          let uu____7938 =
            let uu____7939 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____7939  in
          FStar_Syntax_Syntax.as_arg uu____7938  in
        [uu____7929]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____7928
       in
    uu____7923 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  