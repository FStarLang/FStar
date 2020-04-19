open Prims
let mk_emb :
  'uuuuuu8 .
    (FStar_Range.range -> 'uuuuuu8 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'uuuuuu8 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'uuuuuu8 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____52 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____52
  
let embed :
  'uuuuuu79 .
    'uuuuuu79 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'uuuuuu79 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____99 = FStar_Syntax_Embeddings.embed e x  in
        uu____99 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'uuuuuu117 .
    Prims.bool ->
      'uuuuuu117 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term -> 'uuuuuu117 FStar_Pervasives_Native.option
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
    | (hd,args) ->
        let uu____675 =
          let uu____690 =
            let uu____691 = FStar_Syntax_Util.un_uinst hd  in
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
    | (hd,args) ->
        let uu____1224 =
          let uu____1239 =
            let uu____1240 = FStar_Syntax_Util.un_uinst hd  in
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
      | (hd,args) ->
          let uu____1916 =
            let uu____1929 =
              let uu____1930 = FStar_Syntax_Util.un_uinst hd  in
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
      | FStar_Reflection_Data.Tv_App (hd,a) ->
          let uu____2409 =
            let uu____2414 =
              let uu____2415 =
                let uu____2424 =
                  let uu____2425 = e_term_aq aq  in embed uu____2425 rng hd
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
      | (hd,args) ->
          let uu____3367 =
            let uu____3380 =
              let uu____3381 = FStar_Syntax_Util.un_uinst hd  in
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
  let unembed w t =
    let uu____4295 = unembed' w FStar_Syntax_Embeddings.e_string_list t  in
    FStar_Util.map_opt uu____4295
      (fun p  -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos)
     in
  let uu____4312 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x  -> fun r  -> fun uu____4319  -> fun uu____4320  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____4327  -> unembed w x) uu____4312
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
    | (hd,args) ->
        let uu____4498 =
          let uu____4511 =
            let uu____4512 = FStar_Syntax_Util.un_uinst hd  in
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
    | (hd,args) ->
        let uu____5088 =
          let uu____5101 =
            let uu____5102 = FStar_Syntax_Util.un_uinst hd  in
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
    | (hd,args) ->
        let uu____5554 =
          let uu____5569 =
            let uu____5570 = FStar_Syntax_Util.un_uinst hd  in
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
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_string
      FStar_Syntax_Embeddings.e_range
     in
  FStar_Syntax_Embeddings.embed_as repr FStar_Ident.mk_ident
    (fun i  ->
       let uu____5756 = FStar_Ident.text_of_id i  in
       let uu____5758 = FStar_Ident.range_of_id i  in
       (uu____5756, uu____5758))
    (FStar_Pervasives_Native.Some FStar_Reflection_Data.fstar_refl_ident)
  
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
    | FStar_Reflection_Data.Sg_Let (r,fv,univs,ty,t) ->
        let uu____5793 =
          let uu____5798 =
            let uu____5799 =
              let uu____5808 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5808  in
            let uu____5810 =
              let uu____5821 =
                let uu____5830 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5830  in
              let uu____5831 =
                let uu____5842 =
                  let uu____5851 = embed e_univ_names rng univs  in
                  FStar_Syntax_Syntax.as_arg uu____5851  in
                let uu____5854 =
                  let uu____5865 =
                    let uu____5874 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5874  in
                  let uu____5875 =
                    let uu____5886 =
                      let uu____5895 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5895  in
                    [uu____5886]  in
                  uu____5865 :: uu____5875  in
                uu____5842 :: uu____5854  in
              uu____5821 :: uu____5831  in
            uu____5799 :: uu____5810  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5798
           in
        uu____5793 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5946 =
          let uu____5951 =
            let uu____5952 =
              let uu____5961 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5961  in
            let uu____5965 =
              let uu____5976 =
                let uu____5985 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5985  in
              [uu____5976]  in
            uu____5952 :: uu____5965  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5951
           in
        uu____5946 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs,bs,t,dcs) ->
        let uu____6027 =
          let uu____6032 =
            let uu____6033 =
              let uu____6042 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____6042  in
            let uu____6046 =
              let uu____6057 =
                let uu____6066 = embed e_univ_names rng univs  in
                FStar_Syntax_Syntax.as_arg uu____6066  in
              let uu____6069 =
                let uu____6080 =
                  let uu____6089 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____6089  in
                let uu____6090 =
                  let uu____6101 =
                    let uu____6110 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____6110  in
                  let uu____6111 =
                    let uu____6122 =
                      let uu____6131 =
                        let uu____6132 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____6132 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____6131  in
                    [uu____6122]  in
                  uu____6101 :: uu____6111  in
                uu____6080 :: uu____6090  in
              uu____6057 :: uu____6069  in
            uu____6033 :: uu____6046  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____6032
           in
        uu____6027 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___775_6196 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___775_6196.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___775_6196.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6215 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6215 with
    | (hd,args) ->
        let uu____6260 =
          let uu____6273 =
            let uu____6274 = FStar_Syntax_Util.un_uinst hd  in
            uu____6274.FStar_Syntax_Syntax.n  in
          (uu____6273, args)  in
        (match uu____6260 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____6289)::(us,uu____6291)::(bs,uu____6293)::(t2,uu____6295)::
            (dcs,uu____6297)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____6362 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____6362
               (fun nm1  ->
                  let uu____6380 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____6380
                    (fun us1  ->
                       let uu____6394 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____6394
                         (fun bs1  ->
                            let uu____6400 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____6400
                              (fun t3  ->
                                 let uu____6406 =
                                   let uu____6414 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____6414 dcs  in
                                 FStar_Util.bind_opt uu____6406
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun uu____6444  ->
                                           FStar_Pervasives_Native.Some
                                             uu____6444)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____6453)::(fvar,uu____6455)::(univs,uu____6457)::
            (ty,uu____6459)::(t2,uu____6461)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____6526 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____6526
               (fun r1  ->
                  let uu____6536 = unembed' w e_fv fvar  in
                  FStar_Util.bind_opt uu____6536
                    (fun fvar1  ->
                       let uu____6542 = unembed' w e_univ_names univs  in
                       FStar_Util.bind_opt uu____6542
                         (fun univs1  ->
                            let uu____6556 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____6556
                              (fun ty1  ->
                                 let uu____6562 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____6562
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun uu____6569  ->
                                           FStar_Pervasives_Native.Some
                                             uu____6569)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar1, univs1, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6588 ->
             (if w
              then
                (let uu____6603 =
                   let uu____6609 =
                     let uu____6611 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6611
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6609)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6603)
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
          let uu____6637 =
            let uu____6642 =
              let uu____6643 =
                let uu____6652 =
                  let uu____6653 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6653  in
                FStar_Syntax_Syntax.as_arg uu____6652  in
              [uu____6643]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6642
             in
          uu____6637 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6673 =
            let uu____6678 =
              let uu____6679 =
                let uu____6688 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6688  in
              let uu____6689 =
                let uu____6700 =
                  let uu____6709 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6709  in
                [uu____6700]  in
              uu____6679 :: uu____6689  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6678
             in
          uu____6673 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___850_6734 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___850_6734.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___850_6734.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6755 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6755 with
    | (hd,args) ->
        let uu____6800 =
          let uu____6813 =
            let uu____6814 = FStar_Syntax_Util.un_uinst hd  in
            uu____6814.FStar_Syntax_Syntax.n  in
          (uu____6813, args)  in
        (match uu____6800 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6844)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6869 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6869
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun uu____6876  ->
                       FStar_Pervasives_Native.Some uu____6876)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6879)::(e2,uu____6881)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6916 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6916
               (fun e11  ->
                  let uu____6922 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6922
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun uu____6929  ->
                            FStar_Pervasives_Native.Some uu____6929)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6930 ->
             (if w
              then
                (let uu____6945 =
                   let uu____6951 =
                     let uu____6953 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6953
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6951)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6945)
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
          let uu____6990 =
            let uu____6995 =
              let uu____6996 =
                let uu____7005 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7005  in
              [uu____6996]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
              uu____6995
             in
          uu____6990 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu____7023 =
            let uu____7028 =
              let uu____7029 =
                let uu____7038 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7038  in
              [uu____7029]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
              uu____7028
             in
          uu____7023 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu____7056 =
            let uu____7061 =
              let uu____7062 =
                let uu____7071 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7071  in
              [uu____7062]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
              uu____7061
             in
          uu____7056 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Projector (l,i) ->
          let uu____7090 =
            let uu____7095 =
              let uu____7096 =
                let uu____7105 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7105  in
              let uu____7106 =
                let uu____7117 =
                  let uu____7126 = embed e_ident rng i  in
                  FStar_Syntax_Syntax.as_arg uu____7126  in
                [uu____7117]  in
              uu____7096 :: uu____7106  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
              uu____7095
             in
          uu____7090 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordType (ids1,ids2) ->
          let uu____7161 =
            let uu____7166 =
              let uu____7167 =
                let uu____7176 =
                  let uu____7177 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7177 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____7176  in
              let uu____7184 =
                let uu____7195 =
                  let uu____7204 =
                    let uu____7205 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____7205 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____7204  in
                [uu____7195]  in
              uu____7167 :: uu____7184  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
              uu____7166
             in
          uu____7161 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1,ids2) ->
          let uu____7246 =
            let uu____7251 =
              let uu____7252 =
                let uu____7261 =
                  let uu____7262 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7262 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____7261  in
              let uu____7269 =
                let uu____7280 =
                  let uu____7289 =
                    let uu____7290 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____7290 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____7289  in
                [uu____7280]  in
              uu____7252 :: uu____7269  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
              uu____7251
             in
          uu____7246 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___926_7321 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___926_7321.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___926_7321.FStar_Syntax_Syntax.vars)
    }  in
  let unembed w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____7342 = FStar_Syntax_Util.head_and_args t1  in
    match uu____7342 with
    | (hd,args) ->
        let uu____7387 =
          let uu____7400 =
            let uu____7401 = FStar_Syntax_Util.un_uinst hd  in
            uu____7401.FStar_Syntax_Syntax.n  in
          (uu____7400, args)  in
        (match uu____7387 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7686)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7711 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7711
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun uu____7718  ->
                       FStar_Pervasives_Native.Some uu____7718)
                    (FStar_Reflection_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7721)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7746 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7746
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun uu____7753  ->
                       FStar_Pervasives_Native.Some uu____7753)
                    (FStar_Reflection_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7756)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7781 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7781
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun uu____7788  ->
                       FStar_Pervasives_Native.Some uu____7788)
                    (FStar_Reflection_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7791)::(i,uu____7793)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7828 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7828
               (fun l1  ->
                  let uu____7834 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7834
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun uu____7841  ->
                            FStar_Pervasives_Native.Some uu____7841)
                         (FStar_Reflection_Data.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7844)::(ids2,uu____7846)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7881 =
               let uu____7886 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7886 ids1  in
             FStar_Util.bind_opt uu____7881
               (fun ids11  ->
                  let uu____7900 =
                    let uu____7905 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7905 ids2  in
                  FStar_Util.bind_opt uu____7900
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun uu____7920  ->
                            FStar_Pervasives_Native.Some uu____7920)
                         (FStar_Reflection_Data.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7927)::(ids2,uu____7929)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____7964 =
               let uu____7969 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7969 ids1  in
             FStar_Util.bind_opt uu____7964
               (fun ids11  ->
                  let uu____7983 =
                    let uu____7988 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7988 ids2  in
                  FStar_Util.bind_opt uu____7983
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun uu____8003  ->
                            FStar_Pervasives_Native.Some uu____8003)
                         (FStar_Reflection_Data.RecordConstructor
                            (ids11, ids21))))
         | uu____8008 ->
             (if w
              then
                (let uu____8023 =
                   let uu____8029 =
                     let uu____8031 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____8031
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____8029)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____8023)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed1 unembed FStar_Reflection_Data.fstar_refl_qualifier 
let (e_qualifiers :
  FStar_Reflection_Data.qualifier Prims.list
    FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_qualifier 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8049 =
      let uu____8054 =
        let uu____8055 =
          let uu____8064 =
            let uu____8065 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____8065  in
          FStar_Syntax_Syntax.as_arg uu____8064  in
        [uu____8055]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____8054
       in
    uu____8049 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8089 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____8089 with
    | (bv,aq) ->
        let uu____8096 =
          let uu____8101 =
            let uu____8102 =
              let uu____8111 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____8111  in
            let uu____8112 =
              let uu____8123 =
                let uu____8132 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____8132  in
              [uu____8123]  in
            uu____8102 :: uu____8112  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____8101
           in
        uu____8096 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8164 =
      let uu____8169 =
        let uu____8170 =
          let uu____8179 =
            let uu____8180 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____8187 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____8180 i.FStar_Syntax_Syntax.rng uu____8187  in
          FStar_Syntax_Syntax.as_arg uu____8179  in
        [uu____8170]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____8169
       in
    uu____8164 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8217 =
      let uu____8222 =
        let uu____8223 =
          let uu____8232 =
            let uu____8233 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____8233  in
          FStar_Syntax_Syntax.as_arg uu____8232  in
        [uu____8223]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____8222
       in
    uu____8217 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
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
    let uu____8269 =
      let uu____8274 =
        let uu____8275 =
          let uu____8284 =
            let uu____8285 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____8285  in
          FStar_Syntax_Syntax.as_arg uu____8284  in
        [uu____8275]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____8274
       in
    uu____8269 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  