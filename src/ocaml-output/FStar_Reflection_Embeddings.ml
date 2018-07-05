open Prims
let mk_emb :
  'Auu____9 .
    (FStar_Range.range -> 'Auu____9 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term -> 'Auu____9 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____9 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____51 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____51
  
let embed :
  'Auu____97 .
    'Auu____97 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____97 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____117 = FStar_Syntax_Embeddings.embed e x  in
        uu____117 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____157 .
    Prims.bool ->
      'Auu____157 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____157 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____179 = FStar_Syntax_Embeddings.unembed e x  in
        uu____179 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____218 =
      let uu____219 = FStar_Syntax_Subst.compress t  in
      uu____219.FStar_Syntax_Syntax.n  in
    match uu____218 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____225;
          FStar_Syntax_Syntax.rng = uu____226;_}
        ->
        let uu____229 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____229
    | uu____230 ->
        (if w
         then
           (let uu____232 =
              let uu____237 =
                let uu____238 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____238  in
              (FStar_Errors.Warning_NotEmbedded, uu____237)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____232)
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
    let uu____268 =
      let uu____269 = FStar_Syntax_Subst.compress t  in
      uu____269.FStar_Syntax_Syntax.n  in
    match uu____268 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____275;
          FStar_Syntax_Syntax.rng = uu____276;_}
        ->
        let uu____279 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____279
    | uu____280 ->
        (if w
         then
           (let uu____282 =
              let uu____287 =
                let uu____288 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____288  in
              (FStar_Errors.Warning_NotEmbedded, uu____287)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____282)
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
          let uu____335 = f x  in
          FStar_Util.bind_opt uu____335
            (fun x1  ->
               let uu____343 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____343
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
        let uu____409 =
          mapM_opt
            (fun uu____422  ->
               match uu____422 with
               | (bv,e) ->
                   let uu____431 = unembed_term w e  in
                   FStar_Util.bind_opt uu____431
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____409
          (fun s  ->
             let uu____445 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____445)
         in
      let uu____446 =
        let uu____447 = FStar_Syntax_Subst.compress t  in
        uu____447.FStar_Syntax_Syntax.n  in
      match uu____446 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____458 ->
          (if w
           then
             (let uu____460 =
                let uu____465 =
                  let uu____466 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____466  in
                (FStar_Errors.Warning_NotEmbedded, uu____465)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____460)
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
          let uu____495 =
            let uu____500 =
              let uu____501 =
                let uu____510 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____510  in
              [uu____501]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____500
             in
          uu____495 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___230_529 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___230_529.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___230_529.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____548 = FStar_Syntax_Util.head_and_args t1  in
    match uu____548 with
    | (hd1,args) ->
        let uu____593 =
          let uu____608 =
            let uu____609 = FStar_Syntax_Util.un_uinst hd1  in
            uu____609.FStar_Syntax_Syntax.n  in
          (uu____608, args)  in
        (match uu____593 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____664)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____699 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____699
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____704 ->
             (if w
              then
                (let uu____720 =
                   let uu____725 =
                     let uu____726 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____726
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____725)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____720)
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
    let uu____758 =
      let uu____759 = FStar_Syntax_Subst.compress t  in
      uu____759.FStar_Syntax_Syntax.n  in
    match uu____758 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____765;
          FStar_Syntax_Syntax.rng = uu____766;_}
        ->
        let uu____769 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____769
    | uu____770 ->
        (if w
         then
           (let uu____772 =
              let uu____777 =
                let uu____778 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____778  in
              (FStar_Errors.Warning_NotEmbedded, uu____777)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____772)
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
    let uu____808 =
      let uu____809 = FStar_Syntax_Subst.compress t  in
      uu____809.FStar_Syntax_Syntax.n  in
    match uu____808 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____815;
          FStar_Syntax_Syntax.rng = uu____816;_}
        ->
        let uu____819 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____819
    | uu____820 ->
        (if w
         then
           (let uu____822 =
              let uu____827 =
                let uu____828 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____828  in
              (FStar_Errors.Warning_NotEmbedded, uu____827)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____822)
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
    let uu____858 =
      let uu____859 = FStar_Syntax_Subst.compress t  in
      uu____859.FStar_Syntax_Syntax.n  in
    match uu____858 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____865;
          FStar_Syntax_Syntax.rng = uu____866;_}
        ->
        let uu____869 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____869
    | uu____870 ->
        (if w
         then
           (let uu____872 =
              let uu____877 =
                let uu____878 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____878  in
              (FStar_Errors.Warning_NotEmbedded, uu____877)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____872)
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
          let uu____899 =
            let uu____904 =
              let uu____905 =
                let uu____914 =
                  let uu____915 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____915  in
                FStar_Syntax_Syntax.as_arg uu____914  in
              [uu____905]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____904
             in
          uu____899 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____935 =
            let uu____940 =
              let uu____941 =
                let uu____950 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____950  in
              [uu____941]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____940
             in
          uu____935 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___231_969 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___231_969.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___231_969.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____988 = FStar_Syntax_Util.head_and_args t1  in
    match uu____988 with
    | (hd1,args) ->
        let uu____1033 =
          let uu____1048 =
            let uu____1049 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1049.FStar_Syntax_Syntax.n  in
          (uu____1048, args)  in
        (match uu____1033 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1123)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1158 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1158
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1167)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1202 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1202
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1209 ->
             (if w
              then
                (let uu____1225 =
                   let uu____1230 =
                     let uu____1231 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1231
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1230)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1225)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1239  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1252 =
            let uu____1257 =
              let uu____1258 =
                let uu____1267 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1267  in
              [uu____1258]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1257
             in
          uu____1252 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1292 =
            let uu____1297 =
              let uu____1298 =
                let uu____1307 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1307  in
              let uu____1308 =
                let uu____1319 =
                  let uu____1328 =
                    let uu____1329 =
                      let uu____1334 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1334  in
                    embed uu____1329 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1328  in
                [uu____1319]  in
              uu____1298 :: uu____1308  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1297
             in
          uu____1292 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1366 =
            let uu____1371 =
              let uu____1372 =
                let uu____1381 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1381  in
              [uu____1372]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1371
             in
          uu____1366 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1401 =
            let uu____1406 =
              let uu____1407 =
                let uu____1416 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1416  in
              [uu____1407]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1406
             in
          uu____1401 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1437 =
            let uu____1442 =
              let uu____1443 =
                let uu____1452 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1452  in
              let uu____1453 =
                let uu____1464 =
                  let uu____1473 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1473  in
                [uu____1464]  in
              uu____1443 :: uu____1453  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1442
             in
          uu____1437 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1516 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1516 with
      | (hd1,args) ->
          let uu____1561 =
            let uu____1574 =
              let uu____1575 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1575.FStar_Syntax_Syntax.n  in
            (uu____1574, args)  in
          (match uu____1561 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1590)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1615 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1615
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1624)::(ps,uu____1626)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1661 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1661
                 (fun f1  ->
                    let uu____1667 =
                      let uu____1672 =
                        let uu____1677 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1677  in
                      unembed' w uu____1672 ps  in
                    FStar_Util.bind_opt uu____1667
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1694)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1719 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1719
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1728)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1753 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1753
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1762)::(t2,uu____1764)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1799 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1799
                 (fun bv1  ->
                    let uu____1805 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1805
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1812 ->
               (if w
                then
                  (let uu____1826 =
                     let uu____1831 =
                       let uu____1832 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1832
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1831)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1826)
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
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1851 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1851
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1865 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1865 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1887 =
            let uu____1892 =
              let uu____1893 =
                let uu____1902 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1902  in
              [uu____1893]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1892
             in
          uu____1887 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1922 =
            let uu____1927 =
              let uu____1928 =
                let uu____1937 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1937  in
              [uu____1928]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1927
             in
          uu____1922 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1957 =
            let uu____1962 =
              let uu____1963 =
                let uu____1972 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1972  in
              [uu____1963]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1962
             in
          uu____1957 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1993 =
            let uu____1998 =
              let uu____1999 =
                let uu____2008 =
                  let uu____2009 = e_term_aq aq  in embed uu____2009 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2008  in
              let uu____2012 =
                let uu____2023 =
                  let uu____2032 =
                    let uu____2033 = e_argv_aq aq  in embed uu____2033 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2032  in
                [uu____2023]  in
              uu____1999 :: uu____2012  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1998
             in
          uu____1993 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2072 =
            let uu____2077 =
              let uu____2078 =
                let uu____2087 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2087  in
              let uu____2088 =
                let uu____2099 =
                  let uu____2108 =
                    let uu____2109 = e_term_aq aq  in embed uu____2109 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2108  in
                [uu____2099]  in
              uu____2078 :: uu____2088  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2077
             in
          uu____2072 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2140 =
            let uu____2145 =
              let uu____2146 =
                let uu____2155 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2155  in
              let uu____2156 =
                let uu____2167 =
                  let uu____2176 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2176  in
                [uu____2167]  in
              uu____2146 :: uu____2156  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2145
             in
          uu____2140 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2204 =
            let uu____2209 =
              let uu____2210 =
                let uu____2219 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2219  in
              [uu____2210]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2209
             in
          uu____2204 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2240 =
            let uu____2245 =
              let uu____2246 =
                let uu____2255 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2255  in
              let uu____2256 =
                let uu____2267 =
                  let uu____2276 =
                    let uu____2277 = e_term_aq aq  in embed uu____2277 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2276  in
                [uu____2267]  in
              uu____2246 :: uu____2256  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2245
             in
          uu____2240 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2307 =
            let uu____2312 =
              let uu____2313 =
                let uu____2322 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2322  in
              [uu____2313]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2312
             in
          uu____2307 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2343 =
            let uu____2348 =
              let uu____2349 =
                let uu____2358 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2358  in
              let uu____2359 =
                let uu____2370 =
                  let uu____2379 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2379  in
                [uu____2370]  in
              uu____2349 :: uu____2359  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2348
             in
          uu____2343 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2414 =
            let uu____2419 =
              let uu____2420 =
                let uu____2429 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2429  in
              let uu____2430 =
                let uu____2441 =
                  let uu____2450 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2450  in
                let uu____2451 =
                  let uu____2462 =
                    let uu____2471 =
                      let uu____2472 = e_term_aq aq  in
                      embed uu____2472 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2471  in
                  let uu____2475 =
                    let uu____2486 =
                      let uu____2495 =
                        let uu____2496 = e_term_aq aq  in
                        embed uu____2496 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2495  in
                    [uu____2486]  in
                  uu____2462 :: uu____2475  in
                uu____2441 :: uu____2451  in
              uu____2420 :: uu____2430  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2419
             in
          uu____2414 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2547 =
            let uu____2552 =
              let uu____2553 =
                let uu____2562 =
                  let uu____2563 = e_term_aq aq  in embed uu____2563 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2562  in
              let uu____2566 =
                let uu____2577 =
                  let uu____2586 =
                    let uu____2587 =
                      let uu____2596 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2596  in
                    embed uu____2587 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2586  in
                [uu____2577]  in
              uu____2553 :: uu____2566  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2552
             in
          uu____2547 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2646 =
            let uu____2651 =
              let uu____2652 =
                let uu____2661 =
                  let uu____2662 = e_term_aq aq  in embed uu____2662 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2661  in
              let uu____2665 =
                let uu____2676 =
                  let uu____2685 =
                    let uu____2686 = e_term_aq aq  in embed uu____2686 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2685  in
                let uu____2689 =
                  let uu____2700 =
                    let uu____2709 =
                      let uu____2710 =
                        let uu____2715 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2715  in
                      embed uu____2710 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2709  in
                  [uu____2700]  in
                uu____2676 :: uu____2689  in
              uu____2652 :: uu____2665  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2651
             in
          uu____2646 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2761 =
            let uu____2766 =
              let uu____2767 =
                let uu____2776 =
                  let uu____2777 = e_term_aq aq  in embed uu____2777 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2776  in
              let uu____2780 =
                let uu____2791 =
                  let uu____2800 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2800  in
                let uu____2801 =
                  let uu____2812 =
                    let uu____2821 =
                      let uu____2822 =
                        let uu____2827 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2827  in
                      embed uu____2822 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2821  in
                  [uu____2812]  in
                uu____2791 :: uu____2801  in
              uu____2767 :: uu____2780  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2766
             in
          uu____2761 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___232_2866 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___232_2866.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___232_2866.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2882 = FStar_Syntax_Util.head_and_args t  in
      match uu____2882 with
      | (hd1,args) ->
          let uu____2927 =
            let uu____2940 =
              let uu____2941 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2941.FStar_Syntax_Syntax.n  in
            (uu____2940, args)  in
          (match uu____2927 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2956)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2981 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2981
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2990)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3015 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3015
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3024)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3049 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3049
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3058)::(r,uu____3060)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3095 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3095
                 (fun l1  ->
                    let uu____3101 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3101
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3110)::(t1,uu____3112)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3147 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3147
                 (fun b1  ->
                    let uu____3153 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3153
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3162)::(t1,uu____3164)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3199 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3199
                 (fun b1  ->
                    let uu____3205 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3205
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3214)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3239 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3239
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3248)::(t1,uu____3250)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3285 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3285
                 (fun b1  ->
                    let uu____3291 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3291
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3300)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3325 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3325
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3334)::(l,uu____3336)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3371 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3371
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3382)::(b,uu____3384)::(t1,uu____3386)::(t2,uu____3388)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3443 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3443
                 (fun r1  ->
                    let uu____3449 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3449
                      (fun b1  ->
                         let uu____3455 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3455
                           (fun t11  ->
                              let uu____3461 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3461
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3470)::(brs,uu____3472)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3507 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3507
                 (fun t2  ->
                    let uu____3513 =
                      let uu____3518 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3518 brs  in
                    FStar_Util.bind_opt uu____3513
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3537)::(t1,uu____3539)::(tacopt,uu____3541)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3586 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3586
                 (fun e1  ->
                    let uu____3592 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3592
                      (fun t2  ->
                         let uu____3598 =
                           let uu____3603 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3603 tacopt  in
                         FStar_Util.bind_opt uu____3598
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3622)::(c,uu____3624)::(tacopt,uu____3626)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3671 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3671
                 (fun e1  ->
                    let uu____3677 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3677
                      (fun c1  ->
                         let uu____3683 =
                           let uu____3688 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3688 tacopt  in
                         FStar_Util.bind_opt uu____3683
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_36  ->
                                   FStar_Pervasives_Native.Some _0_36)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____3722 ->
               (if w
                then
                  (let uu____3736 =
                     let uu____3741 =
                       let uu____3742 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3742
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3741)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3736)
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
    let uu____3765 =
      let uu____3770 =
        let uu____3771 =
          let uu____3780 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3780  in
        let uu____3781 =
          let uu____3792 =
            let uu____3801 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3801  in
          let uu____3802 =
            let uu____3813 =
              let uu____3822 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____3822  in
            [uu____3813]  in
          uu____3792 :: uu____3802  in
        uu____3771 :: uu____3781  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3770
       in
    uu____3765 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3873 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3873 with
    | (hd1,args) ->
        let uu____3918 =
          let uu____3931 =
            let uu____3932 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3932.FStar_Syntax_Syntax.n  in
          (uu____3931, args)  in
        (match uu____3918 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3947)::(idx,uu____3949)::(s,uu____3951)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____3996 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____3996
               (fun nm1  ->
                  let uu____4002 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4002
                    (fun idx1  ->
                       let uu____4008 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4008
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4015 ->
             (if w
              then
                (let uu____4029 =
                   let uu____4034 =
                     let uu____4035 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4035
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4034)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4029)
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
        let uu____4056 =
          let uu____4061 =
            let uu____4062 =
              let uu____4071 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4071  in
            let uu____4072 =
              let uu____4083 =
                let uu____4092 =
                  let uu____4093 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4093 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4092  in
              [uu____4083]  in
            uu____4062 :: uu____4072  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4061
           in
        uu____4056 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4131 =
          let uu____4136 =
            let uu____4137 =
              let uu____4146 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4146  in
            let uu____4147 =
              let uu____4158 =
                let uu____4167 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4167  in
              [uu____4158]  in
            uu____4137 :: uu____4147  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4136
           in
        uu____4131 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___233_4194 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___233_4194.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___233_4194.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4211 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4211 with
    | (hd1,args) ->
        let uu____4256 =
          let uu____4269 =
            let uu____4270 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4270.FStar_Syntax_Syntax.n  in
          (uu____4269, args)  in
        (match uu____4256 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4285)::(md,uu____4287)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4322 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4322
               (fun t3  ->
                  let uu____4328 =
                    let uu____4333 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4333 md  in
                  FStar_Util.bind_opt uu____4328
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4352)::(post,uu____4354)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4389 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4389
               (fun pre1  ->
                  let uu____4395 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4395
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
               FStar_Reflection_Data.C_Unknown
         | uu____4419 ->
             (if w
              then
                (let uu____4433 =
                   let uu____4438 =
                     let uu____4439 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4439
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4438)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4433)
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
    let uu___234_4459 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___234_4459.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___234_4459.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4478 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4478 with
    | (hd1,args) ->
        let uu____4523 =
          let uu____4538 =
            let uu____4539 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4539.FStar_Syntax_Syntax.n  in
          (uu____4538, args)  in
        (match uu____4523 with
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
         | uu____4611 ->
             (if w
              then
                (let uu____4627 =
                   let uu____4632 =
                     let uu____4633 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4633
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4632)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4627)
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
    let uu____4663 =
      let uu____4664 = FStar_Syntax_Subst.compress t  in
      uu____4664.FStar_Syntax_Syntax.n  in
    match uu____4663 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____4670;
          FStar_Syntax_Syntax.rng = uu____4671;_}
        ->
        let uu____4674 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4674
    | uu____4675 ->
        (if w
         then
           (let uu____4677 =
              let uu____4682 =
                let uu____4683 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4683
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4682)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4677)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____4736 uu____4737 =
    let uu____4759 =
      let uu____4764 = FStar_Ident.range_of_id i  in
      let uu____4765 = FStar_Ident.text_of_id i  in (uu____4764, uu____4765)
       in
    embed repr rng uu____4759  in
  let unembed_ident t w uu____4789 =
    let uu____4794 = unembed' w repr t  in
    match uu____4794 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4813 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4813
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____4818 =
    FStar_Syntax_Syntax.t_tuple2_of FStar_Syntax_Syntax.t_range
      FStar_Syntax_Syntax.t_string
     in
  let uu____4819 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident uu____4818
    FStar_Ident.text_of_id uu____4819
  
let (e_univ_name :
  FStar_Syntax_Syntax.univ_name FStar_Syntax_Embeddings.embedding) = e_ident 
let (e_univ_names :
  FStar_Syntax_Syntax.univ_name Prims.list FStar_Syntax_Embeddings.embedding)
  = FStar_Syntax_Embeddings.e_list e_univ_name 
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,univs1,ty,t) ->
        let uu____4852 =
          let uu____4857 =
            let uu____4858 =
              let uu____4867 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____4867  in
            let uu____4868 =
              let uu____4879 =
                let uu____4888 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____4888  in
              let uu____4889 =
                let uu____4900 =
                  let uu____4909 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____4909  in
                let uu____4912 =
                  let uu____4923 =
                    let uu____4932 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____4932  in
                  let uu____4933 =
                    let uu____4944 =
                      let uu____4953 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____4953  in
                    [uu____4944]  in
                  uu____4923 :: uu____4933  in
                uu____4900 :: uu____4912  in
              uu____4879 :: uu____4889  in
            uu____4858 :: uu____4868  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4857
           in
        uu____4852 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5006 =
          let uu____5011 =
            let uu____5012 =
              let uu____5021 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5021  in
            let uu____5024 =
              let uu____5035 =
                let uu____5044 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5044  in
              [uu____5035]  in
            uu____5012 :: uu____5024  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5011
           in
        uu____5006 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5088 =
          let uu____5093 =
            let uu____5094 =
              let uu____5103 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5103  in
            let uu____5106 =
              let uu____5117 =
                let uu____5126 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5126  in
              let uu____5129 =
                let uu____5140 =
                  let uu____5149 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5149  in
                let uu____5150 =
                  let uu____5161 =
                    let uu____5170 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5170  in
                  let uu____5171 =
                    let uu____5182 =
                      let uu____5191 =
                        let uu____5192 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5192 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5191  in
                    [uu____5182]  in
                  uu____5161 :: uu____5171  in
                uu____5140 :: uu____5150  in
              uu____5117 :: uu____5129  in
            uu____5094 :: uu____5106  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5093
           in
        uu____5088 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___235_5255 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___235_5255.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___235_5255.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5272 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5272 with
    | (hd1,args) ->
        let uu____5317 =
          let uu____5330 =
            let uu____5331 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5331.FStar_Syntax_Syntax.n  in
          (uu____5330, args)  in
        (match uu____5317 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5346)::(us,uu____5348)::(bs,uu____5350)::(t2,uu____5352)::
            (dcs,uu____5354)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5419 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5419
               (fun nm1  ->
                  let uu____5433 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5433
                    (fun us1  ->
                       let uu____5447 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5447
                         (fun bs1  ->
                            let uu____5453 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5453
                              (fun t3  ->
                                 let uu____5459 =
                                   let uu____5466 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5466 dcs  in
                                 FStar_Util.bind_opt uu____5459
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_42  ->
                                           FStar_Pervasives_Native.Some _0_42)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5499)::(fvar1,uu____5501)::(univs1,uu____5503)::
            (ty,uu____5505)::(t2,uu____5507)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5572 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5572
               (fun r1  ->
                  let uu____5578 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5578
                    (fun fvar2  ->
                       let uu____5584 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5584
                         (fun univs2  ->
                            let uu____5598 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____5598
                              (fun ty1  ->
                                 let uu____5604 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____5604
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _0_43  ->
                                           FStar_Pervasives_Native.Some _0_43)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____5628 ->
             (if w
              then
                (let uu____5642 =
                   let uu____5647 =
                     let uu____5648 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5648
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5647)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5642)
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
          let uu____5669 =
            let uu____5674 =
              let uu____5675 =
                let uu____5684 =
                  let uu____5685 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5685  in
                FStar_Syntax_Syntax.as_arg uu____5684  in
              [uu____5675]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5674
             in
          uu____5669 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5706 =
            let uu____5711 =
              let uu____5712 =
                let uu____5721 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5721  in
              let uu____5722 =
                let uu____5733 =
                  let uu____5742 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5742  in
                [uu____5733]  in
              uu____5712 :: uu____5722  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5711
             in
          uu____5706 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___236_5769 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___236_5769.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___236_5769.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5788 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5788 with
    | (hd1,args) ->
        let uu____5833 =
          let uu____5846 =
            let uu____5847 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5847.FStar_Syntax_Syntax.n  in
          (uu____5846, args)  in
        (match uu____5833 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5877)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5902 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____5902
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____5911)::(e2,uu____5913)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____5948 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____5948
               (fun e11  ->
                  let uu____5954 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____5954
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____5961 ->
             (if w
              then
                (let uu____5975 =
                   let uu____5980 =
                     let uu____5981 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____5981
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5980)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5975)
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
    let uu____5997 =
      let uu____6002 =
        let uu____6003 =
          let uu____6012 =
            let uu____6013 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____6013  in
          FStar_Syntax_Syntax.as_arg uu____6012  in
        [uu____6003]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____6002
       in
    uu____5997 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6038 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____6038 with
    | (bv,aq) ->
        let uu____6045 =
          let uu____6050 =
            let uu____6051 =
              let uu____6060 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____6060  in
            let uu____6061 =
              let uu____6072 =
                let uu____6081 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____6081  in
              [uu____6072]  in
            uu____6051 :: uu____6061  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____6050
           in
        uu____6045 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6114 =
      let uu____6119 =
        let uu____6120 =
          let uu____6129 =
            let uu____6130 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____6135 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____6130 i.FStar_Syntax_Syntax.rng uu____6135  in
          FStar_Syntax_Syntax.as_arg uu____6129  in
        [uu____6120]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____6119
       in
    uu____6114 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6164 =
      let uu____6169 =
        let uu____6170 =
          let uu____6179 =
            let uu____6180 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____6180  in
          FStar_Syntax_Syntax.as_arg uu____6179  in
        [uu____6170]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____6169
       in
    uu____6164 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6210 =
      let uu____6215 =
        let uu____6216 =
          let uu____6225 =
            let uu____6226 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____6226  in
          FStar_Syntax_Syntax.as_arg uu____6225  in
        [uu____6216]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6215
       in
    uu____6210 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  