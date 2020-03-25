open Prims
let mk_emb :
  'uu____8 .
    (FStar_Range.range -> 'uu____8 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'uu____8 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'uu____8 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____52 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____52
  
let embed :
  'uu____79 .
    'uu____79 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'uu____79 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____99 = FStar_Syntax_Embeddings.embed e x  in
        uu____99 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'uu____117 .
    Prims.bool ->
      'uu____117 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term -> 'uu____117 FStar_Pervasives_Native.option
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
                    (fun uu____1356  ->
                       FStar_Pervasives_Native.Some uu____1356)
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
                    (fun uu____1405  ->
                       FStar_Pervasives_Native.Some uu____1405)
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
                    (fun uu____1450  ->
                       FStar_Pervasives_Native.Some uu____1450)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun uu____1472  -> FStar_Pervasives_Native.Some uu____1472)
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
                    (fun uu____1529  ->
                       FStar_Pervasives_Native.Some uu____1529)
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
                      (fun uu____1977  ->
                         FStar_Pervasives_Native.Some uu____1977)
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
                           (fun uu____2085  ->
                              FStar_Pervasives_Native.Some uu____2085)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2095)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____2120 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2120
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun uu____2127  ->
                         FStar_Pervasives_Native.Some uu____2127)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2130)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____2155 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2155
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun uu____2162  ->
                         FStar_Pervasives_Native.Some uu____2162)
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
                           (fun uu____2215  ->
                              FStar_Pervasives_Native.Some uu____2215)
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
                      (fun uu____3428  ->
                         FStar_Pervasives_Native.Some uu____3428)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3431)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3456 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3456
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun uu____3463  ->
                         FStar_Pervasives_Native.Some uu____3463)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3466)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3491 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3491
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun uu____3498  ->
                         FStar_Pervasives_Native.Some uu____3498)
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
                           (fun uu____3551  ->
                              FStar_Pervasives_Native.Some uu____3551)
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
                           (fun uu____3604  ->
                              FStar_Pervasives_Native.Some uu____3604)
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
                           (fun uu____3657  ->
                              FStar_Pervasives_Native.Some uu____3657)
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
                      (fun uu____3692  ->
                         FStar_Pervasives_Native.Some uu____3692)
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
                           (fun uu____3745  ->
                              FStar_Pervasives_Native.Some uu____3745)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3748)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3773 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3773
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun uu____3780  ->
                         FStar_Pervasives_Native.Some uu____3780)
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
                      (fun uu____3829  ->
                         FStar_Pervasives_Native.Some uu____3829)
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
                                          (fun uu____3953  ->
                                             FStar_Pervasives_Native.Some
                                               uu____3953)
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
                           (fun uu____4022  ->
                              FStar_Pervasives_Native.Some uu____4022)
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
                                (fun uu____4108  ->
                                   FStar_Pervasives_Native.Some uu____4108)
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
                                (fun uu____4194  ->
                                   FStar_Pervasives_Native.Some uu____4194)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun uu____4214  -> FStar_Pervasives_Native.Some uu____4214)
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
                              (fun uu____4599  ->
                                 FStar_Pervasives_Native.Some uu____4599)
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
    | FStar_Reflection_Data.C_Lemma (pre,post,pats) ->
        let uu____4794 =
          let uu____4799 =
            let uu____4800 =
              let uu____4809 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4809  in
            let uu____4810 =
              let uu____4821 =
                let uu____4830 = embed e_term rng post  in
                FStar_Syntax_Syntax.as_arg uu____4830  in
              let uu____4831 =
                let uu____4842 =
                  let uu____4851 = embed e_term rng pats  in
                  FStar_Syntax_Syntax.as_arg uu____4851  in
                [uu____4842]  in
              uu____4821 :: uu____4831  in
            uu____4800 :: uu____4810  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4799
           in
        uu____4794 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Eff (us,eff,res,args) ->
        let uu____4896 =
          let uu____4901 =
            let uu____4902 =
              let uu____4911 = embed FStar_Syntax_Embeddings.e_unit rng ()
                 in
              FStar_Syntax_Syntax.as_arg uu____4911  in
            let uu____4912 =
              let uu____4923 =
                let uu____4932 =
                  embed FStar_Syntax_Embeddings.e_string_list rng eff  in
                FStar_Syntax_Syntax.as_arg uu____4932  in
              let uu____4936 =
                let uu____4947 =
                  let uu____4956 = embed e_term rng res  in
                  FStar_Syntax_Syntax.as_arg uu____4956  in
                let uu____4957 =
                  let uu____4968 =
                    let uu____4977 =
                      let uu____4978 = FStar_Syntax_Embeddings.e_list e_argv
                         in
                      embed uu____4978 rng args  in
                    FStar_Syntax_Syntax.as_arg uu____4977  in
                  [uu____4968]  in
                uu____4947 :: uu____4957  in
              uu____4923 :: uu____4936  in
            uu____4902 :: uu____4912  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.t
            uu____4901
           in
        uu____4896 FStar_Pervasives_Native.None rng
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5043 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5043 with
    | (hd1,args) ->
        let uu____5088 =
          let uu____5101 =
            let uu____5102 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5102.FStar_Syntax_Syntax.n  in
          (uu____5101, args)  in
        (match uu____5088 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____5117)::(md,uu____5119)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____5154 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____5154
               (fun t3  ->
                  let uu____5160 =
                    let uu____5165 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____5165 md  in
                  FStar_Util.bind_opt uu____5160
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun uu____5180  ->
                            FStar_Pervasives_Native.Some uu____5180)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____5185)::(md,uu____5187)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
             ->
             let uu____5222 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____5222
               (fun t3  ->
                  let uu____5228 =
                    let uu____5233 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____5233 md  in
                  FStar_Util.bind_opt uu____5228
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun uu____5248  ->
                            FStar_Pervasives_Native.Some uu____5248)
                         (FStar_Reflection_Data.C_GTotal (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____5253)::(post,uu____5255)::(pats,uu____5257)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____5302 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____5302
               (fun pre1  ->
                  let uu____5308 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____5308
                    (fun post1  ->
                       let uu____5314 = unembed' w e_term pats  in
                       FStar_Util.bind_opt uu____5314
                         (fun pats1  ->
                            FStar_All.pipe_left
                              (fun uu____5321  ->
                                 FStar_Pervasives_Native.Some uu____5321)
                              (FStar_Reflection_Data.C_Lemma
                                 (pre1, post1, pats1)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(us,uu____5324)::(eff,uu____5326)::(res,uu____5328)::(args1,uu____5330)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
             ->
             let uu____5385 = unembed' w FStar_Syntax_Embeddings.e_unit us
                in
             FStar_Util.bind_opt uu____5385
               (fun us1  ->
                  let uu____5391 =
                    unembed' w FStar_Syntax_Embeddings.e_string_list eff  in
                  FStar_Util.bind_opt uu____5391
                    (fun eff1  ->
                       let uu____5409 = unembed' w e_term res  in
                       FStar_Util.bind_opt uu____5409
                         (fun res1  ->
                            let uu____5415 =
                              let uu____5420 =
                                FStar_Syntax_Embeddings.e_list e_argv  in
                              unembed' w uu____5420 args1  in
                            FStar_Util.bind_opt uu____5415
                              (fun args2  ->
                                 FStar_All.pipe_left
                                   (fun uu____5435  ->
                                      FStar_Pervasives_Native.Some uu____5435)
                                   (FStar_Reflection_Data.C_Eff
                                      ([], eff1, res1, args2))))))
         | uu____5440 ->
             (if w
              then
                (let uu____5455 =
                   let uu____5461 =
                     let uu____5463 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____5463
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5461)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5455)
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
    let uu___712_5488 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___712_5488.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___712_5488.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5509 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5509 with
    | (hd1,args) ->
        let uu____5554 =
          let uu____5569 =
            let uu____5570 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5570.FStar_Syntax_Syntax.n  in
          (uu____5569, args)  in
        (match uu____5554 with
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
         | uu____5642 ->
             (if w
              then
                (let uu____5659 =
                   let uu____5665 =
                     let uu____5667 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____5667
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5665)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5659)
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
    let uu____5704 =
      let uu____5705 = FStar_Syntax_Subst.compress t  in
      uu____5705.FStar_Syntax_Syntax.n  in
    match uu____5704 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5711;
          FStar_Syntax_Syntax.rng = uu____5712;_}
        ->
        let uu____5715 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5715
    | uu____5716 ->
        (if w
         then
           (let uu____5719 =
              let uu____5725 =
                let uu____5727 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5727
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5725)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5719)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____5767 uu____5768 =
    let uu____5770 =
      let uu____5776 = FStar_Ident.range_of_id i  in
      let uu____5777 = FStar_Ident.text_of_id i  in (uu____5776, uu____5777)
       in
    embed repr rng uu____5770  in
  let unembed_ident t w uu____5804 =
    let uu____5809 = unembed' w repr t  in
    match uu____5809 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5833 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5833
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5840 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5840
  
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
        let uu____5879 =
          let uu____5884 =
            let uu____5885 =
              let uu____5894 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5894  in
            let uu____5896 =
              let uu____5907 =
                let uu____5916 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5916  in
              let uu____5917 =
                let uu____5928 =
                  let uu____5937 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5937  in
                let uu____5940 =
                  let uu____5951 =
                    let uu____5960 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5960  in
                  let uu____5961 =
                    let uu____5972 =
                      let uu____5981 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5981  in
                    [uu____5972]  in
                  uu____5951 :: uu____5961  in
                uu____5928 :: uu____5940  in
              uu____5907 :: uu____5917  in
            uu____5885 :: uu____5896  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5884
           in
        uu____5879 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____6032 =
          let uu____6037 =
            let uu____6038 =
              let uu____6047 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____6047  in
            let uu____6051 =
              let uu____6062 =
                let uu____6071 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____6071  in
              [uu____6062]  in
            uu____6038 :: uu____6051  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____6037
           in
        uu____6032 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____6113 =
          let uu____6118 =
            let uu____6119 =
              let uu____6128 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____6128  in
            let uu____6132 =
              let uu____6143 =
                let uu____6152 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____6152  in
              let uu____6155 =
                let uu____6166 =
                  let uu____6175 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____6175  in
                let uu____6176 =
                  let uu____6187 =
                    let uu____6196 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____6196  in
                  let uu____6197 =
                    let uu____6208 =
                      let uu____6217 =
                        let uu____6218 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____6218 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____6217  in
                    [uu____6208]  in
                  uu____6187 :: uu____6197  in
                uu____6166 :: uu____6176  in
              uu____6143 :: uu____6155  in
            uu____6119 :: uu____6132  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____6118
           in
        uu____6113 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___788_6282 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___788_6282.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___788_6282.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6301 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6301 with
    | (hd1,args) ->
        let uu____6346 =
          let uu____6359 =
            let uu____6360 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6360.FStar_Syntax_Syntax.n  in
          (uu____6359, args)  in
        (match uu____6346 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____6375)::(us,uu____6377)::(bs,uu____6379)::(t2,uu____6381)::
            (dcs,uu____6383)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____6448 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____6448
               (fun nm1  ->
                  let uu____6466 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____6466
                    (fun us1  ->
                       let uu____6480 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____6480
                         (fun bs1  ->
                            let uu____6486 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____6486
                              (fun t3  ->
                                 let uu____6492 =
                                   let uu____6500 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____6500 dcs  in
                                 FStar_Util.bind_opt uu____6492
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun uu____6530  ->
                                           FStar_Pervasives_Native.Some
                                             uu____6530)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____6539)::(fvar1,uu____6541)::(univs1,uu____6543)::
            (ty,uu____6545)::(t2,uu____6547)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____6612 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____6612
               (fun r1  ->
                  let uu____6622 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____6622
                    (fun fvar2  ->
                       let uu____6628 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____6628
                         (fun univs2  ->
                            let uu____6642 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____6642
                              (fun ty1  ->
                                 let uu____6648 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____6648
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun uu____6655  ->
                                           FStar_Pervasives_Native.Some
                                             uu____6655)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6674 ->
             (if w
              then
                (let uu____6689 =
                   let uu____6695 =
                     let uu____6697 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6697
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6695)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6689)
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
          let uu____6723 =
            let uu____6728 =
              let uu____6729 =
                let uu____6738 =
                  let uu____6739 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6739  in
                FStar_Syntax_Syntax.as_arg uu____6738  in
              [uu____6729]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6728
             in
          uu____6723 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6759 =
            let uu____6764 =
              let uu____6765 =
                let uu____6774 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6774  in
              let uu____6775 =
                let uu____6786 =
                  let uu____6795 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6795  in
                [uu____6786]  in
              uu____6765 :: uu____6775  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6764
             in
          uu____6759 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___863_6820 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___863_6820.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___863_6820.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6841 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6841 with
    | (hd1,args) ->
        let uu____6886 =
          let uu____6899 =
            let uu____6900 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6900.FStar_Syntax_Syntax.n  in
          (uu____6899, args)  in
        (match uu____6886 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6930)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6955 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6955
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun uu____6962  ->
                       FStar_Pervasives_Native.Some uu____6962)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6965)::(e2,uu____6967)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____7002 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____7002
               (fun e11  ->
                  let uu____7008 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____7008
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun uu____7015  ->
                            FStar_Pervasives_Native.Some uu____7015)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____7016 ->
             (if w
              then
                (let uu____7031 =
                   let uu____7037 =
                     let uu____7039 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____7039
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____7037)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7031)
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
          let uu____7076 =
            let uu____7081 =
              let uu____7082 =
                let uu____7091 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7091  in
              [uu____7082]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
              uu____7081
             in
          uu____7076 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu____7109 =
            let uu____7114 =
              let uu____7115 =
                let uu____7124 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7124  in
              [uu____7115]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
              uu____7114
             in
          uu____7109 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu____7142 =
            let uu____7147 =
              let uu____7148 =
                let uu____7157 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7157  in
              [uu____7148]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
              uu____7147
             in
          uu____7142 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Projector (l,i) ->
          let uu____7176 =
            let uu____7181 =
              let uu____7182 =
                let uu____7191 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7191  in
              let uu____7192 =
                let uu____7203 =
                  let uu____7212 = embed e_ident rng i  in
                  FStar_Syntax_Syntax.as_arg uu____7212  in
                [uu____7203]  in
              uu____7182 :: uu____7192  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
              uu____7181
             in
          uu____7176 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordType (ids1,ids2) ->
          let uu____7247 =
            let uu____7252 =
              let uu____7253 =
                let uu____7262 =
                  let uu____7263 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7263 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____7262  in
              let uu____7270 =
                let uu____7281 =
                  let uu____7290 =
                    let uu____7291 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____7291 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____7290  in
                [uu____7281]  in
              uu____7253 :: uu____7270  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
              uu____7252
             in
          uu____7247 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1,ids2) ->
          let uu____7332 =
            let uu____7337 =
              let uu____7338 =
                let uu____7347 =
                  let uu____7348 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7348 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____7347  in
              let uu____7355 =
                let uu____7366 =
                  let uu____7375 =
                    let uu____7376 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____7376 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____7375  in
                [uu____7366]  in
              uu____7338 :: uu____7355  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
              uu____7337
             in
          uu____7332 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___939_7407 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___939_7407.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___939_7407.FStar_Syntax_Syntax.vars)
    }  in
  let unembed1 w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____7428 = FStar_Syntax_Util.head_and_args t1  in
    match uu____7428 with
    | (hd1,args) ->
        let uu____7473 =
          let uu____7486 =
            let uu____7487 = FStar_Syntax_Util.un_uinst hd1  in
            uu____7487.FStar_Syntax_Syntax.n  in
          (uu____7486, args)  in
        (match uu____7473 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7772)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7797 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7797
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun uu____7804  ->
                       FStar_Pervasives_Native.Some uu____7804)
                    (FStar_Reflection_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7807)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7832 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7832
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun uu____7839  ->
                       FStar_Pervasives_Native.Some uu____7839)
                    (FStar_Reflection_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7842)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7867 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7867
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun uu____7874  ->
                       FStar_Pervasives_Native.Some uu____7874)
                    (FStar_Reflection_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7877)::(i,uu____7879)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7914 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7914
               (fun l1  ->
                  let uu____7920 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7920
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun uu____7927  ->
                            FStar_Pervasives_Native.Some uu____7927)
                         (FStar_Reflection_Data.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7930)::(ids2,uu____7932)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7967 =
               let uu____7972 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7972 ids1  in
             FStar_Util.bind_opt uu____7967
               (fun ids11  ->
                  let uu____7986 =
                    let uu____7991 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7991 ids2  in
                  FStar_Util.bind_opt uu____7986
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun uu____8006  ->
                            FStar_Pervasives_Native.Some uu____8006)
                         (FStar_Reflection_Data.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____8013)::(ids2,uu____8015)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____8050 =
               let uu____8055 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____8055 ids1  in
             FStar_Util.bind_opt uu____8050
               (fun ids11  ->
                  let uu____8069 =
                    let uu____8074 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____8074 ids2  in
                  FStar_Util.bind_opt uu____8069
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun uu____8089  ->
                            FStar_Pervasives_Native.Some uu____8089)
                         (FStar_Reflection_Data.RecordConstructor
                            (ids11, ids21))))
         | uu____8094 ->
             (if w
              then
                (let uu____8109 =
                   let uu____8115 =
                     let uu____8117 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____8117
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____8115)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____8109)
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
    let uu____8135 =
      let uu____8140 =
        let uu____8141 =
          let uu____8150 =
            let uu____8151 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____8151  in
          FStar_Syntax_Syntax.as_arg uu____8150  in
        [uu____8141]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____8140
       in
    uu____8135 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8175 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____8175 with
    | (bv,aq) ->
        let uu____8182 =
          let uu____8187 =
            let uu____8188 =
              let uu____8197 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____8197  in
            let uu____8198 =
              let uu____8209 =
                let uu____8218 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____8218  in
              [uu____8209]  in
            uu____8188 :: uu____8198  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____8187
           in
        uu____8182 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8250 =
      let uu____8255 =
        let uu____8256 =
          let uu____8265 =
            let uu____8266 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____8273 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____8266 i.FStar_Syntax_Syntax.rng uu____8273  in
          FStar_Syntax_Syntax.as_arg uu____8265  in
        [uu____8256]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____8255
       in
    uu____8250 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8303 =
      let uu____8308 =
        let uu____8309 =
          let uu____8318 =
            let uu____8319 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____8319  in
          FStar_Syntax_Syntax.as_arg uu____8318  in
        [uu____8309]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____8308
       in
    uu____8303 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
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
    let uu____8355 =
      let uu____8360 =
        let uu____8361 =
          let uu____8370 =
            let uu____8371 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____8371  in
          FStar_Syntax_Syntax.as_arg uu____8370  in
        [uu____8361]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____8360
       in
    uu____8355 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  