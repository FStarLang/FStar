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
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (t, qi)) rng  in
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
            let uu____578 =
              let uu____587 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____587  in
            [uu____578]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
            uu____577 FStar_Range.dummyRange
       in
    let uu___104_604 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___104_604.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___104_604.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____625 = FStar_Syntax_Util.head_and_args t1  in
    match uu____625 with
    | (hd,args) ->
        let uu____670 =
          let uu____685 =
            let uu____686 = FStar_Syntax_Util.un_uinst hd  in
            uu____686.FStar_Syntax_Syntax.n  in
          (uu____685, args)  in
        (match uu____670 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____741)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____776 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____776
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____781 ->
             (if w
              then
                (let uu____798 =
                   let uu____804 =
                     let uu____806 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____806
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____804)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____798)
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
    let uu____846 =
      let uu____847 = FStar_Syntax_Subst.compress t  in
      uu____847.FStar_Syntax_Syntax.n  in
    match uu____846 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____853;
          FStar_Syntax_Syntax.rng = uu____854;_}
        ->
        let uu____857 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____857
    | uu____858 ->
        (if w
         then
           (let uu____861 =
              let uu____867 =
                let uu____869 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____869  in
              (FStar_Errors.Warning_NotEmbedded, uu____867)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____861)
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
    let uu____906 =
      let uu____907 = FStar_Syntax_Subst.compress t  in
      uu____907.FStar_Syntax_Syntax.n  in
    match uu____906 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____913;
          FStar_Syntax_Syntax.rng = uu____914;_}
        ->
        let uu____917 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____917
    | uu____918 ->
        (if w
         then
           (let uu____921 =
              let uu____927 =
                let uu____929 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____929  in
              (FStar_Errors.Warning_NotEmbedded, uu____927)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____921)
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
    let uu____966 =
      let uu____967 = FStar_Syntax_Subst.compress t  in
      uu____967.FStar_Syntax_Syntax.n  in
    match uu____966 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____973;
          FStar_Syntax_Syntax.rng = uu____974;_}
        ->
        let uu____977 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____977
    | uu____978 ->
        (if w
         then
           (let uu____981 =
              let uu____987 =
                let uu____989 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____989  in
              (FStar_Errors.Warning_NotEmbedded, uu____987)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____981)
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
          let uu____1015 =
            let uu____1016 =
              let uu____1025 =
                let uu____1026 = FStar_BigInt.string_of_big_int i  in
                FStar_Syntax_Util.exp_int uu____1026  in
              FStar_Syntax_Syntax.as_arg uu____1025  in
            [uu____1016]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
            uu____1015 FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____1046 =
            let uu____1047 =
              let uu____1056 = embed FStar_Syntax_Embeddings.e_string rng s
                 in
              FStar_Syntax_Syntax.as_arg uu____1056  in
            [uu____1047]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
            uu____1046 FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____1075 =
            let uu____1076 =
              let uu____1085 = embed FStar_Syntax_Embeddings.e_range rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____1085  in
            [uu____1076]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
            uu____1075 FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____1103 =
            let uu____1104 =
              let uu____1113 =
                embed FStar_Syntax_Embeddings.e_string_list rng ns  in
              FStar_Syntax_Syntax.as_arg uu____1113  in
            [uu____1104]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
            uu____1103 FStar_Range.dummyRange
       in
    let uu___193_1133 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___193_1133.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___193_1133.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1154 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1154 with
    | (hd,args) ->
        let uu____1199 =
          let uu____1214 =
            let uu____1215 = FStar_Syntax_Util.un_uinst hd  in
            uu____1215.FStar_Syntax_Syntax.n  in
          (uu____1214, args)  in
        (match uu____1199 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1289)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1324 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1324
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun uu____1331  ->
                       FStar_Pervasives_Native.Some uu____1331)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1334)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1369 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1369
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun uu____1380  ->
                       FStar_Pervasives_Native.Some uu____1380)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____1383)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1418 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____1418
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun uu____1425  ->
                       FStar_Pervasives_Native.Some uu____1425)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun uu____1447  -> FStar_Pervasives_Native.Some uu____1447)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____1450)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____1485 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____1485
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun uu____1504  ->
                       FStar_Pervasives_Native.Some uu____1504)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____1505 ->
             (if w
              then
                (let uu____1522 =
                   let uu____1528 =
                     let uu____1530 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1530
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1528)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1522)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1543  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1556 =
            let uu____1557 =
              let uu____1566 = embed e_const rng c  in
              FStar_Syntax_Syntax.as_arg uu____1566  in
            [uu____1557]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
            uu____1556 rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1599 =
            let uu____1600 =
              let uu____1609 = embed e_fv rng fv  in
              FStar_Syntax_Syntax.as_arg uu____1609  in
            let uu____1610 =
              let uu____1621 =
                let uu____1630 =
                  let uu____1631 =
                    let uu____1641 =
                      let uu____1649 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_tuple2 uu____1649
                        FStar_Syntax_Embeddings.e_bool
                       in
                    FStar_Syntax_Embeddings.e_list uu____1641  in
                  embed uu____1631 rng ps  in
                FStar_Syntax_Syntax.as_arg uu____1630  in
              [uu____1621]  in
            uu____1600 :: uu____1610  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
            uu____1599 rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1690 =
            let uu____1691 =
              let uu____1700 = embed e_bv rng bv  in
              FStar_Syntax_Syntax.as_arg uu____1700  in
            [uu____1691]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
            uu____1690 rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1718 =
            let uu____1719 =
              let uu____1728 = embed e_bv rng bv  in
              FStar_Syntax_Syntax.as_arg uu____1728  in
            [uu____1719]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
            uu____1718 rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1747 =
            let uu____1748 =
              let uu____1757 = embed e_bv rng bv  in
              FStar_Syntax_Syntax.as_arg uu____1757  in
            let uu____1758 =
              let uu____1769 =
                let uu____1778 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____1778  in
              [uu____1769]  in
            uu____1748 :: uu____1758  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
            uu____1747 rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1821 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1821 with
      | (hd,args) ->
          let uu____1866 =
            let uu____1879 =
              let uu____1880 = FStar_Syntax_Util.un_uinst hd  in
              uu____1880.FStar_Syntax_Syntax.n  in
            (uu____1879, args)  in
          (match uu____1866 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1895)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1920 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1920
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun uu____1927  ->
                         FStar_Pervasives_Native.Some uu____1927)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1930)::(ps,uu____1932)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1967 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1967
                 (fun f1  ->
                    let uu____1973 =
                      let uu____1983 =
                        let uu____1993 =
                          let uu____2001 = e_pattern' ()  in
                          FStar_Syntax_Embeddings.e_tuple2 uu____2001
                            FStar_Syntax_Embeddings.e_bool
                           in
                        FStar_Syntax_Embeddings.e_list uu____1993  in
                      unembed' w uu____1983 ps  in
                    FStar_Util.bind_opt uu____1973
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun uu____2035  ->
                              FStar_Pervasives_Native.Some uu____2035)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2045)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____2070 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2070
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun uu____2077  ->
                         FStar_Pervasives_Native.Some uu____2077)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2080)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____2105 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2105
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun uu____2112  ->
                         FStar_Pervasives_Native.Some uu____2112)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____2115)::(t2,uu____2117)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____2152 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2152
                 (fun bv1  ->
                    let uu____2158 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____2158
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun uu____2165  ->
                              FStar_Pervasives_Native.Some uu____2165)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2166 ->
               (if w
                then
                  (let uu____2181 =
                     let uu____2187 =
                       let uu____2189 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2189
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2187)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2181)
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
    let uu____2221 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2221
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2236 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2236 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2259 =
            let uu____2260 =
              let uu____2269 = embed e_fv rng fv  in
              FStar_Syntax_Syntax.as_arg uu____2269  in
            [uu____2260]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
            uu____2259 rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2287 =
            let uu____2288 =
              let uu____2297 = embed e_bv rng fv  in
              FStar_Syntax_Syntax.as_arg uu____2297  in
            [uu____2288]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
            uu____2287 rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2315 =
            let uu____2316 =
              let uu____2325 = embed e_bv rng bv  in
              FStar_Syntax_Syntax.as_arg uu____2325  in
            [uu____2316]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
            uu____2315 rng
      | FStar_Reflection_Data.Tv_App (hd,a) ->
          let uu____2344 =
            let uu____2345 =
              let uu____2354 =
                let uu____2355 = e_term_aq aq  in embed uu____2355 rng hd  in
              FStar_Syntax_Syntax.as_arg uu____2354  in
            let uu____2358 =
              let uu____2369 =
                let uu____2378 =
                  let uu____2379 = e_argv_aq aq  in embed uu____2379 rng a
                   in
                FStar_Syntax_Syntax.as_arg uu____2378  in
              [uu____2369]  in
            uu____2345 :: uu____2358  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
            uu____2344 rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2416 =
            let uu____2417 =
              let uu____2426 = embed e_binder rng b  in
              FStar_Syntax_Syntax.as_arg uu____2426  in
            let uu____2427 =
              let uu____2438 =
                let uu____2447 =
                  let uu____2448 = e_term_aq aq  in embed uu____2448 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2447  in
              [uu____2438]  in
            uu____2417 :: uu____2427  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
            uu____2416 rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2477 =
            let uu____2478 =
              let uu____2487 = embed e_binder rng b  in
              FStar_Syntax_Syntax.as_arg uu____2487  in
            let uu____2488 =
              let uu____2499 =
                let uu____2508 = embed e_comp rng c  in
                FStar_Syntax_Syntax.as_arg uu____2508  in
              [uu____2499]  in
            uu____2478 :: uu____2488  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
            uu____2477 rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2534 =
            let uu____2535 =
              let uu____2544 = embed FStar_Syntax_Embeddings.e_unit rng ()
                 in
              FStar_Syntax_Syntax.as_arg uu____2544  in
            [uu____2535]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
            uu____2534 rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2563 =
            let uu____2564 =
              let uu____2573 = embed e_bv rng bv  in
              FStar_Syntax_Syntax.as_arg uu____2573  in
            let uu____2574 =
              let uu____2585 =
                let uu____2594 =
                  let uu____2595 = e_term_aq aq  in embed uu____2595 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2594  in
              [uu____2585]  in
            uu____2564 :: uu____2574  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
            uu____2563 rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2623 =
            let uu____2624 =
              let uu____2633 = embed e_const rng c  in
              FStar_Syntax_Syntax.as_arg uu____2633  in
            [uu____2624]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
            uu____2623 rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2652 =
            let uu____2653 =
              let uu____2662 = embed FStar_Syntax_Embeddings.e_int rng u  in
              FStar_Syntax_Syntax.as_arg uu____2662  in
            let uu____2663 =
              let uu____2674 =
                let uu____2683 =
                  FStar_Syntax_Util.mk_lazy (u, d)
                    FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.as_arg uu____2683  in
              [uu____2674]  in
            uu____2653 :: uu____2663  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
            uu____2652 rng
      | FStar_Reflection_Data.Tv_Let (r,attrs,b,t1,t2) ->
          let uu____2723 =
            let uu____2724 =
              let uu____2733 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____2733  in
            let uu____2735 =
              let uu____2746 =
                let uu____2755 =
                  let uu____2756 = FStar_Syntax_Embeddings.e_list e_term  in
                  embed uu____2756 rng attrs  in
                FStar_Syntax_Syntax.as_arg uu____2755  in
              let uu____2763 =
                let uu____2774 =
                  let uu____2783 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2783  in
                let uu____2784 =
                  let uu____2795 =
                    let uu____2804 =
                      let uu____2805 = e_term_aq aq  in
                      embed uu____2805 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2804  in
                  let uu____2808 =
                    let uu____2819 =
                      let uu____2828 =
                        let uu____2829 = e_term_aq aq  in
                        embed uu____2829 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2828  in
                    [uu____2819]  in
                  uu____2795 :: uu____2808  in
                uu____2774 :: uu____2784  in
              uu____2746 :: uu____2763  in
            uu____2724 :: uu____2735  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
            uu____2723 rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2886 =
            let uu____2887 =
              let uu____2896 =
                let uu____2897 = e_term_aq aq  in embed uu____2897 rng t1  in
              FStar_Syntax_Syntax.as_arg uu____2896  in
            let uu____2900 =
              let uu____2911 =
                let uu____2920 =
                  let uu____2921 =
                    let uu____2930 = e_branch_aq aq  in
                    FStar_Syntax_Embeddings.e_list uu____2930  in
                  embed uu____2921 rng brs  in
                FStar_Syntax_Syntax.as_arg uu____2920  in
              [uu____2911]  in
            uu____2887 :: uu____2900  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
            uu____2886 rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2978 =
            let uu____2979 =
              let uu____2988 =
                let uu____2989 = e_term_aq aq  in embed uu____2989 rng e  in
              FStar_Syntax_Syntax.as_arg uu____2988  in
            let uu____2992 =
              let uu____3003 =
                let uu____3012 =
                  let uu____3013 = e_term_aq aq  in embed uu____3013 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____3012  in
              let uu____3016 =
                let uu____3027 =
                  let uu____3036 =
                    let uu____3037 =
                      let uu____3042 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.e_option uu____3042  in
                    embed uu____3037 rng tacopt  in
                  FStar_Syntax_Syntax.as_arg uu____3036  in
                [uu____3027]  in
              uu____3003 :: uu____3016  in
            uu____2979 :: uu____2992  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
            uu____2978 rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____3086 =
            let uu____3087 =
              let uu____3096 =
                let uu____3097 = e_term_aq aq  in embed uu____3097 rng e  in
              FStar_Syntax_Syntax.as_arg uu____3096  in
            let uu____3100 =
              let uu____3111 =
                let uu____3120 = embed e_comp rng c  in
                FStar_Syntax_Syntax.as_arg uu____3120  in
              let uu____3121 =
                let uu____3132 =
                  let uu____3141 =
                    let uu____3142 =
                      let uu____3147 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.e_option uu____3147  in
                    embed uu____3142 rng tacopt  in
                  FStar_Syntax_Syntax.as_arg uu____3141  in
                [uu____3132]  in
              uu____3111 :: uu____3121  in
            uu____3087 :: uu____3100  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
            uu____3086 rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___387_3184 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___387_3184.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___387_3184.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3202 = FStar_Syntax_Util.head_and_args t  in
      match uu____3202 with
      | (hd,args) ->
          let uu____3247 =
            let uu____3260 =
              let uu____3261 = FStar_Syntax_Util.un_uinst hd  in
              uu____3261.FStar_Syntax_Syntax.n  in
            (uu____3260, args)  in
          (match uu____3247 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3276)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3301 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3301
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun uu____3308  ->
                         FStar_Pervasives_Native.Some uu____3308)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3311)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3336 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3336
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun uu____3343  ->
                         FStar_Pervasives_Native.Some uu____3343)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3346)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3371 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3371
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun uu____3378  ->
                         FStar_Pervasives_Native.Some uu____3378)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3381)::(r,uu____3383)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3418 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3418
                 (fun l1  ->
                    let uu____3424 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3424
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun uu____3431  ->
                              FStar_Pervasives_Native.Some uu____3431)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3434)::(t1,uu____3436)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3471 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3471
                 (fun b1  ->
                    let uu____3477 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3477
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun uu____3484  ->
                              FStar_Pervasives_Native.Some uu____3484)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3487)::(t1,uu____3489)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3524 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3524
                 (fun b1  ->
                    let uu____3530 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3530
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun uu____3537  ->
                              FStar_Pervasives_Native.Some uu____3537)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3540)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3565 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3565
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun uu____3572  ->
                         FStar_Pervasives_Native.Some uu____3572)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3575)::(t1,uu____3577)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3612 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3612
                 (fun b1  ->
                    let uu____3618 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3618
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun uu____3625  ->
                              FStar_Pervasives_Native.Some uu____3625)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3628)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3653 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3653
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun uu____3660  ->
                         FStar_Pervasives_Native.Some uu____3660)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3663)::(l,uu____3665)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3700 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3700
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun uu____3709  ->
                         FStar_Pervasives_Native.Some uu____3709)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3712)::(attrs,uu____3714)::(b,uu____3716)::
              (t1,uu____3718)::(t2,uu____3720)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3785 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3785
                 (fun r1  ->
                    let uu____3795 =
                      let uu____3800 = FStar_Syntax_Embeddings.e_list e_term
                         in
                      unembed' w uu____3800 attrs  in
                    FStar_Util.bind_opt uu____3795
                      (fun attrs1  ->
                         let uu____3814 = unembed' w e_bv b  in
                         FStar_Util.bind_opt uu____3814
                           (fun b1  ->
                              let uu____3820 = unembed' w e_term t1  in
                              FStar_Util.bind_opt uu____3820
                                (fun t11  ->
                                   let uu____3826 = unembed' w e_term t2  in
                                   FStar_Util.bind_opt uu____3826
                                     (fun t21  ->
                                        FStar_All.pipe_left
                                          (fun uu____3833  ->
                                             FStar_Pervasives_Native.Some
                                               uu____3833)
                                          (FStar_Reflection_Data.Tv_Let
                                             (r1, attrs1, b1, t11, t21)))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3839)::(brs,uu____3841)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3876 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3876
                 (fun t2  ->
                    let uu____3882 =
                      let uu____3887 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3887 brs  in
                    FStar_Util.bind_opt uu____3882
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun uu____3902  ->
                              FStar_Pervasives_Native.Some uu____3902)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3907)::(t1,uu____3909)::(tacopt,uu____3911)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3956 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3956
                 (fun e1  ->
                    let uu____3962 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3962
                      (fun t2  ->
                         let uu____3968 =
                           let uu____3973 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3973 tacopt  in
                         FStar_Util.bind_opt uu____3968
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun uu____3988  ->
                                   FStar_Pervasives_Native.Some uu____3988)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3993)::(c,uu____3995)::(tacopt,uu____3997)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____4042 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4042
                 (fun e1  ->
                    let uu____4048 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____4048
                      (fun c1  ->
                         let uu____4054 =
                           let uu____4059 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4059 tacopt  in
                         FStar_Util.bind_opt uu____4054
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun uu____4074  ->
                                   FStar_Pervasives_Native.Some uu____4074)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun uu____4094  -> FStar_Pervasives_Native.Some uu____4094)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____4095 ->
               (if w
                then
                  (let uu____4110 =
                     let uu____4116 =
                       let uu____4118 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4118
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4116)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____4110)
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
    let uu____4147 = FStar_Ident.path_of_lid lid  in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____4147  in
  let unembed w t =
    let uu____4175 = unembed' w FStar_Syntax_Embeddings.e_string_list t  in
    FStar_Util.map_opt uu____4175
      (fun p  -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos)
     in
  let uu____4192 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x  -> fun r  -> fun uu____4199  -> fun uu____4200  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____4207  -> unembed w x) uu____4192
    FStar_Ident.string_of_lid FStar_Syntax_Syntax.ET_abstract
  
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____4224 =
      let uu____4225 =
        let uu____4234 =
          embed FStar_Syntax_Embeddings.e_string rng
            bvv.FStar_Reflection_Data.bv_ppname
           in
        FStar_Syntax_Syntax.as_arg uu____4234  in
      let uu____4236 =
        let uu____4247 =
          let uu____4256 =
            embed FStar_Syntax_Embeddings.e_int rng
              bvv.FStar_Reflection_Data.bv_index
             in
          FStar_Syntax_Syntax.as_arg uu____4256  in
        let uu____4257 =
          let uu____4268 =
            let uu____4277 =
              embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
            FStar_Syntax_Syntax.as_arg uu____4277  in
          [uu____4268]  in
        uu____4247 :: uu____4257  in
      uu____4225 :: uu____4236  in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4224 rng
     in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4328 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4328 with
    | (hd,args) ->
        let uu____4373 =
          let uu____4386 =
            let uu____4387 = FStar_Syntax_Util.un_uinst hd  in
            uu____4387.FStar_Syntax_Syntax.n  in
          (uu____4386, args)  in
        (match uu____4373 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4402)::(idx,uu____4404)::(s,uu____4406)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4451 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4451
               (fun nm1  ->
                  let uu____4461 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4461
                    (fun idx1  ->
                       let uu____4467 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4467
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun uu____4474  ->
                                 FStar_Pervasives_Native.Some uu____4474)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4475 ->
             (if w
              then
                (let uu____4490 =
                   let uu____4496 =
                     let uu____4498 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4498
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4496)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4490)
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
        let uu____4524 =
          let uu____4525 =
            let uu____4534 = embed e_term rng t  in
            FStar_Syntax_Syntax.as_arg uu____4534  in
          let uu____4535 =
            let uu____4546 =
              let uu____4555 =
                let uu____4556 = FStar_Syntax_Embeddings.e_option e_term  in
                embed uu____4556 rng md  in
              FStar_Syntax_Syntax.as_arg uu____4555  in
            [uu____4546]  in
          uu____4525 :: uu____4535  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
          uu____4524 rng
    | FStar_Reflection_Data.C_GTotal (t,md) ->
        let uu____4593 =
          let uu____4594 =
            let uu____4603 = embed e_term rng t  in
            FStar_Syntax_Syntax.as_arg uu____4603  in
          let uu____4604 =
            let uu____4615 =
              let uu____4624 =
                let uu____4625 = FStar_Syntax_Embeddings.e_option e_term  in
                embed uu____4625 rng md  in
              FStar_Syntax_Syntax.as_arg uu____4624  in
            [uu____4615]  in
          uu____4594 :: uu____4604  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.t
          uu____4593 rng
    | FStar_Reflection_Data.C_Lemma (pre,post,pats) ->
        let uu____4659 =
          let uu____4660 =
            let uu____4669 = embed e_term rng pre  in
            FStar_Syntax_Syntax.as_arg uu____4669  in
          let uu____4670 =
            let uu____4681 =
              let uu____4690 = embed e_term rng post  in
              FStar_Syntax_Syntax.as_arg uu____4690  in
            let uu____4691 =
              let uu____4702 =
                let uu____4711 = embed e_term rng pats  in
                FStar_Syntax_Syntax.as_arg uu____4711  in
              [uu____4702]  in
            uu____4681 :: uu____4691  in
          uu____4660 :: uu____4670  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
          uu____4659 rng
    | FStar_Reflection_Data.C_Eff (us,eff,res,args) ->
        let uu____4756 =
          let uu____4757 =
            let uu____4766 = embed FStar_Syntax_Embeddings.e_unit rng ()  in
            FStar_Syntax_Syntax.as_arg uu____4766  in
          let uu____4767 =
            let uu____4778 =
              let uu____4787 =
                embed FStar_Syntax_Embeddings.e_string_list rng eff  in
              FStar_Syntax_Syntax.as_arg uu____4787  in
            let uu____4791 =
              let uu____4802 =
                let uu____4811 = embed e_term rng res  in
                FStar_Syntax_Syntax.as_arg uu____4811  in
              let uu____4812 =
                let uu____4823 =
                  let uu____4832 =
                    let uu____4833 = FStar_Syntax_Embeddings.e_list e_argv
                       in
                    embed uu____4833 rng args  in
                  FStar_Syntax_Syntax.as_arg uu____4832  in
                [uu____4823]  in
              uu____4802 :: uu____4812  in
            uu____4778 :: uu____4791  in
          uu____4757 :: uu____4767  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.t uu____4756
          rng
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4898 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4898 with
    | (hd,args) ->
        let uu____4943 =
          let uu____4956 =
            let uu____4957 = FStar_Syntax_Util.un_uinst hd  in
            uu____4957.FStar_Syntax_Syntax.n  in
          (uu____4956, args)  in
        (match uu____4943 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4972)::(md,uu____4974)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____5009 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____5009
               (fun t3  ->
                  let uu____5015 =
                    let uu____5020 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____5020 md  in
                  FStar_Util.bind_opt uu____5015
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun uu____5035  ->
                            FStar_Pervasives_Native.Some uu____5035)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____5040)::(md,uu____5042)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
             ->
             let uu____5077 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____5077
               (fun t3  ->
                  let uu____5083 =
                    let uu____5088 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____5088 md  in
                  FStar_Util.bind_opt uu____5083
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun uu____5103  ->
                            FStar_Pervasives_Native.Some uu____5103)
                         (FStar_Reflection_Data.C_GTotal (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____5108)::(post,uu____5110)::(pats,uu____5112)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____5157 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____5157
               (fun pre1  ->
                  let uu____5163 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____5163
                    (fun post1  ->
                       let uu____5169 = unembed' w e_term pats  in
                       FStar_Util.bind_opt uu____5169
                         (fun pats1  ->
                            FStar_All.pipe_left
                              (fun uu____5176  ->
                                 FStar_Pervasives_Native.Some uu____5176)
                              (FStar_Reflection_Data.C_Lemma
                                 (pre1, post1, pats1)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(us,uu____5179)::(eff,uu____5181)::(res,uu____5183)::(args1,uu____5185)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
             ->
             let uu____5240 = unembed' w FStar_Syntax_Embeddings.e_unit us
                in
             FStar_Util.bind_opt uu____5240
               (fun us1  ->
                  let uu____5246 =
                    unembed' w FStar_Syntax_Embeddings.e_string_list eff  in
                  FStar_Util.bind_opt uu____5246
                    (fun eff1  ->
                       let uu____5264 = unembed' w e_term res  in
                       FStar_Util.bind_opt uu____5264
                         (fun res1  ->
                            let uu____5270 =
                              let uu____5275 =
                                FStar_Syntax_Embeddings.e_list e_argv  in
                              unembed' w uu____5275 args1  in
                            FStar_Util.bind_opt uu____5270
                              (fun args2  ->
                                 FStar_All.pipe_left
                                   (fun uu____5290  ->
                                      FStar_Pervasives_Native.Some uu____5290)
                                   (FStar_Reflection_Data.C_Eff
                                      ([], eff1, res1, args2))))))
         | uu____5295 ->
             (if w
              then
                (let uu____5310 =
                   let uu____5316 =
                     let uu____5318 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____5318
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5316)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5310)
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
    let uu___712_5343 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___712_5343.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___712_5343.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5364 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5364 with
    | (hd,args) ->
        let uu____5409 =
          let uu____5424 =
            let uu____5425 = FStar_Syntax_Util.un_uinst hd  in
            uu____5425.FStar_Syntax_Syntax.n  in
          (uu____5424, args)  in
        (match uu____5409 with
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
         | uu____5497 ->
             (if w
              then
                (let uu____5514 =
                   let uu____5520 =
                     let uu____5522 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____5522
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5520)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5514)
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
    let uu____5559 =
      let uu____5560 = FStar_Syntax_Subst.compress t  in
      uu____5560.FStar_Syntax_Syntax.n  in
    match uu____5559 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5566;
          FStar_Syntax_Syntax.rng = uu____5567;_}
        ->
        let uu____5570 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5570
    | uu____5571 ->
        (if w
         then
           (let uu____5574 =
              let uu____5580 =
                let uu____5582 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5582
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5580)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5574)
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
       let uu____5611 = FStar_Ident.text_of_id i  in
       let uu____5613 = FStar_Ident.range_of_id i  in
       (uu____5611, uu____5613))
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
        let uu____5648 =
          let uu____5649 =
            let uu____5658 = embed FStar_Syntax_Embeddings.e_bool rng r  in
            FStar_Syntax_Syntax.as_arg uu____5658  in
          let uu____5660 =
            let uu____5671 =
              let uu____5680 = embed e_fv rng fv  in
              FStar_Syntax_Syntax.as_arg uu____5680  in
            let uu____5681 =
              let uu____5692 =
                let uu____5701 = embed e_univ_names rng univs  in
                FStar_Syntax_Syntax.as_arg uu____5701  in
              let uu____5704 =
                let uu____5715 =
                  let uu____5724 = embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____5724  in
                let uu____5725 =
                  let uu____5736 =
                    let uu____5745 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5745  in
                  [uu____5736]  in
                uu____5715 :: uu____5725  in
              uu____5692 :: uu____5704  in
            uu____5671 :: uu____5681  in
          uu____5649 :: uu____5660  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t uu____5648
          rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5796 =
          let uu____5797 =
            let uu____5806 =
              embed FStar_Syntax_Embeddings.e_string_list rng nm  in
            FStar_Syntax_Syntax.as_arg uu____5806  in
          let uu____5810 =
            let uu____5821 =
              let uu____5830 = embed e_term rng ty  in
              FStar_Syntax_Syntax.as_arg uu____5830  in
            [uu____5821]  in
          uu____5797 :: uu____5810  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
          uu____5796 rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs,bs,t,dcs) ->
        let uu____5872 =
          let uu____5873 =
            let uu____5882 =
              embed FStar_Syntax_Embeddings.e_string_list rng nm  in
            FStar_Syntax_Syntax.as_arg uu____5882  in
          let uu____5886 =
            let uu____5897 =
              let uu____5906 = embed e_univ_names rng univs  in
              FStar_Syntax_Syntax.as_arg uu____5906  in
            let uu____5909 =
              let uu____5920 =
                let uu____5929 = embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____5929  in
              let uu____5930 =
                let uu____5941 =
                  let uu____5950 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____5950  in
                let uu____5951 =
                  let uu____5962 =
                    let uu____5971 =
                      let uu____5972 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      embed uu____5972 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____5971  in
                  [uu____5962]  in
                uu____5941 :: uu____5951  in
              uu____5920 :: uu____5930  in
            uu____5897 :: uu____5909  in
          uu____5873 :: uu____5886  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
          uu____5872 rng
    | FStar_Reflection_Data.Unk  ->
        let uu___775_6036 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___775_6036.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___775_6036.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6055 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6055 with
    | (hd,args) ->
        let uu____6100 =
          let uu____6113 =
            let uu____6114 = FStar_Syntax_Util.un_uinst hd  in
            uu____6114.FStar_Syntax_Syntax.n  in
          (uu____6113, args)  in
        (match uu____6100 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____6129)::(us,uu____6131)::(bs,uu____6133)::(t2,uu____6135)::
            (dcs,uu____6137)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____6202 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____6202
               (fun nm1  ->
                  let uu____6220 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____6220
                    (fun us1  ->
                       let uu____6234 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____6234
                         (fun bs1  ->
                            let uu____6240 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____6240
                              (fun t3  ->
                                 let uu____6246 =
                                   let uu____6254 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____6254 dcs  in
                                 FStar_Util.bind_opt uu____6246
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun uu____6284  ->
                                           FStar_Pervasives_Native.Some
                                             uu____6284)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____6293)::(fvar,uu____6295)::(univs,uu____6297)::
            (ty,uu____6299)::(t2,uu____6301)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____6366 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____6366
               (fun r1  ->
                  let uu____6376 = unembed' w e_fv fvar  in
                  FStar_Util.bind_opt uu____6376
                    (fun fvar1  ->
                       let uu____6382 = unembed' w e_univ_names univs  in
                       FStar_Util.bind_opt uu____6382
                         (fun univs1  ->
                            let uu____6396 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____6396
                              (fun ty1  ->
                                 let uu____6402 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____6402
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun uu____6409  ->
                                           FStar_Pervasives_Native.Some
                                             uu____6409)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar1, univs1, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6428 ->
             (if w
              then
                (let uu____6443 =
                   let uu____6449 =
                     let uu____6451 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6451
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6449)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6443)
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
          let uu____6477 =
            let uu____6478 =
              let uu____6487 =
                let uu____6488 = FStar_BigInt.string_of_big_int i  in
                FStar_Syntax_Util.exp_int uu____6488  in
              FStar_Syntax_Syntax.as_arg uu____6487  in
            [uu____6478]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
            uu____6477 FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6508 =
            let uu____6509 =
              let uu____6518 = embed_exp rng e1  in
              FStar_Syntax_Syntax.as_arg uu____6518  in
            let uu____6519 =
              let uu____6530 =
                let uu____6539 = embed_exp rng e2  in
                FStar_Syntax_Syntax.as_arg uu____6539  in
              [uu____6530]  in
            uu____6509 :: uu____6519  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
            uu____6508 FStar_Range.dummyRange
       in
    let uu___850_6564 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___850_6564.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___850_6564.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6585 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6585 with
    | (hd,args) ->
        let uu____6630 =
          let uu____6643 =
            let uu____6644 = FStar_Syntax_Util.un_uinst hd  in
            uu____6644.FStar_Syntax_Syntax.n  in
          (uu____6643, args)  in
        (match uu____6630 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6674)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6699 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6699
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun uu____6706  ->
                       FStar_Pervasives_Native.Some uu____6706)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6709)::(e2,uu____6711)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6746 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6746
               (fun e11  ->
                  let uu____6752 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6752
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun uu____6759  ->
                            FStar_Pervasives_Native.Some uu____6759)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6760 ->
             (if w
              then
                (let uu____6775 =
                   let uu____6781 =
                     let uu____6783 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6783
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6781)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6775)
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
          let uu____6820 =
            let uu____6821 =
              let uu____6830 = embed e_lid rng l  in
              FStar_Syntax_Syntax.as_arg uu____6830  in
            [uu____6821]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
            uu____6820 FStar_Range.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu____6848 =
            let uu____6849 =
              let uu____6858 = embed e_lid rng l  in
              FStar_Syntax_Syntax.as_arg uu____6858  in
            [uu____6849]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
            uu____6848 FStar_Range.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu____6876 =
            let uu____6877 =
              let uu____6886 = embed e_lid rng l  in
              FStar_Syntax_Syntax.as_arg uu____6886  in
            [uu____6877]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
            uu____6876 FStar_Range.dummyRange
      | FStar_Reflection_Data.Projector (l,i) ->
          let uu____6905 =
            let uu____6906 =
              let uu____6915 = embed e_lid rng l  in
              FStar_Syntax_Syntax.as_arg uu____6915  in
            let uu____6916 =
              let uu____6927 =
                let uu____6936 = embed e_ident rng i  in
                FStar_Syntax_Syntax.as_arg uu____6936  in
              [uu____6927]  in
            uu____6906 :: uu____6916  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
            uu____6905 FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordType (ids1,ids2) ->
          let uu____6971 =
            let uu____6972 =
              let uu____6981 =
                let uu____6982 = FStar_Syntax_Embeddings.e_list e_ident  in
                embed uu____6982 rng ids1  in
              FStar_Syntax_Syntax.as_arg uu____6981  in
            let uu____6989 =
              let uu____7000 =
                let uu____7009 =
                  let uu____7010 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7010 rng ids2  in
                FStar_Syntax_Syntax.as_arg uu____7009  in
              [uu____7000]  in
            uu____6972 :: uu____6989  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
            uu____6971 FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1,ids2) ->
          let uu____7051 =
            let uu____7052 =
              let uu____7061 =
                let uu____7062 = FStar_Syntax_Embeddings.e_list e_ident  in
                embed uu____7062 rng ids1  in
              FStar_Syntax_Syntax.as_arg uu____7061  in
            let uu____7069 =
              let uu____7080 =
                let uu____7089 =
                  let uu____7090 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7090 rng ids2  in
                FStar_Syntax_Syntax.as_arg uu____7089  in
              [uu____7080]  in
            uu____7052 :: uu____7069  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
            uu____7051 FStar_Range.dummyRange
       in
    let uu___926_7121 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___926_7121.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___926_7121.FStar_Syntax_Syntax.vars)
    }  in
  let unembed w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____7142 = FStar_Syntax_Util.head_and_args t1  in
    match uu____7142 with
    | (hd,args) ->
        let uu____7187 =
          let uu____7200 =
            let uu____7201 = FStar_Syntax_Util.un_uinst hd  in
            uu____7201.FStar_Syntax_Syntax.n  in
          (uu____7200, args)  in
        (match uu____7187 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7486)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7511 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7511
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun uu____7518  ->
                       FStar_Pervasives_Native.Some uu____7518)
                    (FStar_Reflection_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7521)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7546 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7546
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun uu____7553  ->
                       FStar_Pervasives_Native.Some uu____7553)
                    (FStar_Reflection_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7556)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7581 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7581
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun uu____7588  ->
                       FStar_Pervasives_Native.Some uu____7588)
                    (FStar_Reflection_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7591)::(i,uu____7593)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7628 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7628
               (fun l1  ->
                  let uu____7634 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7634
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun uu____7641  ->
                            FStar_Pervasives_Native.Some uu____7641)
                         (FStar_Reflection_Data.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7644)::(ids2,uu____7646)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7681 =
               let uu____7686 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7686 ids1  in
             FStar_Util.bind_opt uu____7681
               (fun ids11  ->
                  let uu____7700 =
                    let uu____7705 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7705 ids2  in
                  FStar_Util.bind_opt uu____7700
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun uu____7720  ->
                            FStar_Pervasives_Native.Some uu____7720)
                         (FStar_Reflection_Data.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7727)::(ids2,uu____7729)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____7764 =
               let uu____7769 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7769 ids1  in
             FStar_Util.bind_opt uu____7764
               (fun ids11  ->
                  let uu____7783 =
                    let uu____7788 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7788 ids2  in
                  FStar_Util.bind_opt uu____7783
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun uu____7803  ->
                            FStar_Pervasives_Native.Some uu____7803)
                         (FStar_Reflection_Data.RecordConstructor
                            (ids11, ids21))))
         | uu____7808 ->
             (if w
              then
                (let uu____7823 =
                   let uu____7829 =
                     let uu____7831 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____7831
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____7829)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7823)
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
    let uu____7849 =
      let uu____7850 =
        let uu____7859 =
          let uu____7860 = FStar_Reflection_Basic.inspect_bv bv  in
          embed e_bv_view i.FStar_Syntax_Syntax.rng uu____7860  in
        FStar_Syntax_Syntax.as_arg uu____7859  in
      [uu____7850]  in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
      uu____7849 i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7884 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____7884 with
    | (bv,aq) ->
        let uu____7891 =
          let uu____7892 =
            let uu____7901 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
            FStar_Syntax_Syntax.as_arg uu____7901  in
          let uu____7902 =
            let uu____7913 =
              let uu____7922 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                 in
              FStar_Syntax_Syntax.as_arg uu____7922  in
            [uu____7913]  in
          uu____7892 :: uu____7902  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
          uu____7891 i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____7954 =
      let uu____7955 =
        let uu____7964 =
          let uu____7965 =
            FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
             in
          let uu____7972 = FStar_Reflection_Basic.inspect_fv fv  in
          embed uu____7965 i.FStar_Syntax_Syntax.rng uu____7972  in
        FStar_Syntax_Syntax.as_arg uu____7964  in
      [uu____7955]  in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
      uu____7954 i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8002 =
      let uu____8003 =
        let uu____8012 =
          let uu____8013 = FStar_Reflection_Basic.inspect_comp comp  in
          embed e_comp_view i.FStar_Syntax_Syntax.rng uu____8013  in
        FStar_Syntax_Syntax.as_arg uu____8012  in
      [uu____8003]  in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
      uu____8002 i.FStar_Syntax_Syntax.rng
  
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
    let uu____8049 =
      let uu____8050 =
        let uu____8059 =
          let uu____8060 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
          embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____8060  in
        FStar_Syntax_Syntax.as_arg uu____8059  in
      [uu____8050]  in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
      uu____8049 i.FStar_Syntax_Syntax.rng
  