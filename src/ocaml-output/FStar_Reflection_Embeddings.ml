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
            (fun uu____426  ->
               match uu____426 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____449 = unembed_term w e  in
                      FStar_Util.bind_opt uu____449
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1))))) aq1
           in
        FStar_Util.bind_opt uu____409
          (fun s  ->
             let uu____463 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____463)
         in
      let uu____464 =
        let uu____465 = FStar_Syntax_Subst.compress t  in
        uu____465.FStar_Syntax_Syntax.n  in
      match uu____464 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____476 ->
          (if w
           then
             (let uu____478 =
                let uu____483 =
                  let uu____484 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____484  in
                (FStar_Errors.Warning_NotEmbedded, uu____483)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____478)
           else ();
           FStar_Pervasives_Native.None)
       in
    mk_emb embed_term unembed_term FStar_Syntax_Syntax.t_term
  
let (e_term : FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding) =
  e_term_aq [] 
let (e_term_nbe_aq :
  (FStar_Syntax_Syntax.bv,Prims.bool,FStar_Syntax_Syntax.term'
                                       FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding)
  =
  fun aq  ->
    let embed_term t =
      let qi =
        {
          FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
          FStar_Syntax_Syntax.antiquotes = aq
        }  in
      FStar_TypeChecker_NBETerm.Quote (t, qi)  in
    let rec unembed_term t =
      match t with
      | FStar_TypeChecker_NBETerm.Quote (tm,qi) ->
          FStar_Pervasives_Native.Some tm
      | uu____544 -> FStar_Pervasives_Native.None  in
    let fv_term = FStar_Syntax_Syntax.fvconst FStar_Parser_Const.term_lid  in
    {
      FStar_TypeChecker_NBETerm.em = embed_term;
      FStar_TypeChecker_NBETerm.un = unembed_term;
      FStar_TypeChecker_NBETerm.typ =
        (FStar_TypeChecker_NBETerm.FV (fv_term, [], []))
    }
  
let (e_term_nbe :
  FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding) =
  e_term_nbe_aq [] 
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
          let uu____587 =
            let uu____592 =
              let uu____593 =
                let uu____602 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____602  in
              [uu____593]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____592
             in
          uu____587 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___229_621 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___229_621.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___229_621.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____640 = FStar_Syntax_Util.head_and_args t1  in
    match uu____640 with
    | (hd1,args) ->
        let uu____685 =
          let uu____700 =
            let uu____701 = FStar_Syntax_Util.un_uinst hd1  in
            uu____701.FStar_Syntax_Syntax.n  in
          (uu____700, args)  in
        (match uu____685 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____756)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____791 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____791
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____796 ->
             (if w
              then
                (let uu____812 =
                   let uu____817 =
                     let uu____818 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____818
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____817)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____812)
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
    let uu____850 =
      let uu____851 = FStar_Syntax_Subst.compress t  in
      uu____851.FStar_Syntax_Syntax.n  in
    match uu____850 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____857;
          FStar_Syntax_Syntax.rng = uu____858;_}
        ->
        let uu____861 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____861
    | uu____862 ->
        (if w
         then
           (let uu____864 =
              let uu____869 =
                let uu____870 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____870  in
              (FStar_Errors.Warning_NotEmbedded, uu____869)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____864)
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
    let uu____900 =
      let uu____901 = FStar_Syntax_Subst.compress t  in
      uu____901.FStar_Syntax_Syntax.n  in
    match uu____900 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____907;
          FStar_Syntax_Syntax.rng = uu____908;_}
        ->
        let uu____911 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____911
    | uu____912 ->
        (if w
         then
           (let uu____914 =
              let uu____919 =
                let uu____920 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____920  in
              (FStar_Errors.Warning_NotEmbedded, uu____919)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____914)
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
    let uu____950 =
      let uu____951 = FStar_Syntax_Subst.compress t  in
      uu____951.FStar_Syntax_Syntax.n  in
    match uu____950 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____957;
          FStar_Syntax_Syntax.rng = uu____958;_}
        ->
        let uu____961 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____961
    | uu____962 ->
        (if w
         then
           (let uu____964 =
              let uu____969 =
                let uu____970 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____970  in
              (FStar_Errors.Warning_NotEmbedded, uu____969)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____964)
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
          let uu____991 =
            let uu____996 =
              let uu____997 =
                let uu____1006 =
                  let uu____1007 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____1007  in
                FStar_Syntax_Syntax.as_arg uu____1006  in
              [uu____997]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____996
             in
          uu____991 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____1027 =
            let uu____1032 =
              let uu____1033 =
                let uu____1042 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____1042  in
              [uu____1033]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____1032
             in
          uu____1027 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___230_1061 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___230_1061.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___230_1061.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1080 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1080 with
    | (hd1,args) ->
        let uu____1125 =
          let uu____1140 =
            let uu____1141 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1141.FStar_Syntax_Syntax.n  in
          (uu____1140, args)  in
        (match uu____1125 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1215)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1250 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1250
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1259)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1294 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1294
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1301 ->
             (if w
              then
                (let uu____1317 =
                   let uu____1322 =
                     let uu____1323 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1323
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1322)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1317)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1331  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1344 =
            let uu____1349 =
              let uu____1350 =
                let uu____1359 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1359  in
              [uu____1350]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1349
             in
          uu____1344 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1384 =
            let uu____1389 =
              let uu____1390 =
                let uu____1399 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1399  in
              let uu____1400 =
                let uu____1411 =
                  let uu____1420 =
                    let uu____1421 =
                      let uu____1426 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1426  in
                    embed uu____1421 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1420  in
                [uu____1411]  in
              uu____1390 :: uu____1400  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1389
             in
          uu____1384 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1458 =
            let uu____1463 =
              let uu____1464 =
                let uu____1473 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1473  in
              [uu____1464]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1463
             in
          uu____1458 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1493 =
            let uu____1498 =
              let uu____1499 =
                let uu____1508 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1508  in
              [uu____1499]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1498
             in
          uu____1493 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1529 =
            let uu____1534 =
              let uu____1535 =
                let uu____1544 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1544  in
              let uu____1545 =
                let uu____1556 =
                  let uu____1565 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1565  in
                [uu____1556]  in
              uu____1535 :: uu____1545  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1534
             in
          uu____1529 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1608 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1608 with
      | (hd1,args) ->
          let uu____1653 =
            let uu____1666 =
              let uu____1667 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1667.FStar_Syntax_Syntax.n  in
            (uu____1666, args)  in
          (match uu____1653 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1682)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1707 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1707
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1716)::(ps,uu____1718)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1753 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1753
                 (fun f1  ->
                    let uu____1759 =
                      let uu____1764 =
                        let uu____1769 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1769  in
                      unembed' w uu____1764 ps  in
                    FStar_Util.bind_opt uu____1759
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1786)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1811 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1811
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1820)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1845 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1845
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1854)::(t2,uu____1856)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1891 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1891
                 (fun bv1  ->
                    let uu____1897 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1897
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1904 ->
               (if w
                then
                  (let uu____1918 =
                     let uu____1923 =
                       let uu____1924 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1924
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1923)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1918)
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
    let uu____1943 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1943
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1957 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1957 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1979 =
            let uu____1984 =
              let uu____1985 =
                let uu____1994 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1994  in
              [uu____1985]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1984
             in
          uu____1979 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2014 =
            let uu____2019 =
              let uu____2020 =
                let uu____2029 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2029  in
              [uu____2020]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2019
             in
          uu____2014 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2049 =
            let uu____2054 =
              let uu____2055 =
                let uu____2064 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2064  in
              [uu____2055]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2054
             in
          uu____2049 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2085 =
            let uu____2090 =
              let uu____2091 =
                let uu____2100 =
                  let uu____2101 = e_term_aq aq  in embed uu____2101 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2100  in
              let uu____2104 =
                let uu____2115 =
                  let uu____2124 =
                    let uu____2125 = e_argv_aq aq  in embed uu____2125 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2124  in
                [uu____2115]  in
              uu____2091 :: uu____2104  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2090
             in
          uu____2085 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2164 =
            let uu____2169 =
              let uu____2170 =
                let uu____2179 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2179  in
              let uu____2180 =
                let uu____2191 =
                  let uu____2200 =
                    let uu____2201 = e_term_aq aq  in embed uu____2201 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2200  in
                [uu____2191]  in
              uu____2170 :: uu____2180  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2169
             in
          uu____2164 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2232 =
            let uu____2237 =
              let uu____2238 =
                let uu____2247 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2247  in
              let uu____2248 =
                let uu____2259 =
                  let uu____2268 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2268  in
                [uu____2259]  in
              uu____2238 :: uu____2248  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2237
             in
          uu____2232 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2296 =
            let uu____2301 =
              let uu____2302 =
                let uu____2311 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2311  in
              [uu____2302]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2301
             in
          uu____2296 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2332 =
            let uu____2337 =
              let uu____2338 =
                let uu____2347 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2347  in
              let uu____2348 =
                let uu____2359 =
                  let uu____2368 =
                    let uu____2369 = e_term_aq aq  in embed uu____2369 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2368  in
                [uu____2359]  in
              uu____2338 :: uu____2348  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2337
             in
          uu____2332 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2399 =
            let uu____2404 =
              let uu____2405 =
                let uu____2414 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2414  in
              [uu____2405]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2404
             in
          uu____2399 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2435 =
            let uu____2440 =
              let uu____2441 =
                let uu____2450 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2450  in
              let uu____2451 =
                let uu____2462 =
                  let uu____2471 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2471  in
                [uu____2462]  in
              uu____2441 :: uu____2451  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2440
             in
          uu____2435 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2506 =
            let uu____2511 =
              let uu____2512 =
                let uu____2521 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2521  in
              let uu____2522 =
                let uu____2533 =
                  let uu____2542 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2542  in
                let uu____2543 =
                  let uu____2554 =
                    let uu____2563 =
                      let uu____2564 = e_term_aq aq  in
                      embed uu____2564 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2563  in
                  let uu____2567 =
                    let uu____2578 =
                      let uu____2587 =
                        let uu____2588 = e_term_aq aq  in
                        embed uu____2588 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2587  in
                    [uu____2578]  in
                  uu____2554 :: uu____2567  in
                uu____2533 :: uu____2543  in
              uu____2512 :: uu____2522  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2511
             in
          uu____2506 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2639 =
            let uu____2644 =
              let uu____2645 =
                let uu____2654 =
                  let uu____2655 = e_term_aq aq  in embed uu____2655 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2654  in
              let uu____2658 =
                let uu____2669 =
                  let uu____2678 =
                    let uu____2679 =
                      let uu____2688 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2688  in
                    embed uu____2679 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2678  in
                [uu____2669]  in
              uu____2645 :: uu____2658  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2644
             in
          uu____2639 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2738 =
            let uu____2743 =
              let uu____2744 =
                let uu____2753 =
                  let uu____2754 = e_term_aq aq  in embed uu____2754 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2753  in
              let uu____2757 =
                let uu____2768 =
                  let uu____2777 =
                    let uu____2778 = e_term_aq aq  in embed uu____2778 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2777  in
                let uu____2781 =
                  let uu____2792 =
                    let uu____2801 =
                      let uu____2802 =
                        let uu____2807 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2807  in
                      embed uu____2802 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2801  in
                  [uu____2792]  in
                uu____2768 :: uu____2781  in
              uu____2744 :: uu____2757  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2743
             in
          uu____2738 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2853 =
            let uu____2858 =
              let uu____2859 =
                let uu____2868 =
                  let uu____2869 = e_term_aq aq  in embed uu____2869 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2868  in
              let uu____2872 =
                let uu____2883 =
                  let uu____2892 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2892  in
                let uu____2893 =
                  let uu____2904 =
                    let uu____2913 =
                      let uu____2914 =
                        let uu____2919 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2919  in
                      embed uu____2914 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2913  in
                  [uu____2904]  in
                uu____2883 :: uu____2893  in
              uu____2859 :: uu____2872  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2858
             in
          uu____2853 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___231_2958 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___231_2958.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___231_2958.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2974 = FStar_Syntax_Util.head_and_args t  in
      match uu____2974 with
      | (hd1,args) ->
          let uu____3019 =
            let uu____3032 =
              let uu____3033 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3033.FStar_Syntax_Syntax.n  in
            (uu____3032, args)  in
          (match uu____3019 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3048)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3073 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3073
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3082)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3107 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3107
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3116)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3141 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3141
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3150)::(r,uu____3152)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3187 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3187
                 (fun l1  ->
                    let uu____3193 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3193
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3202)::(t1,uu____3204)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3239 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3239
                 (fun b1  ->
                    let uu____3245 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3245
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3254)::(t1,uu____3256)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3291 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3291
                 (fun b1  ->
                    let uu____3297 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3297
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3306)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3331 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3331
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3340)::(t1,uu____3342)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3377 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3377
                 (fun b1  ->
                    let uu____3383 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3383
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3392)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3417 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3417
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3426)::(l,uu____3428)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3463 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3463
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3474)::(b,uu____3476)::(t1,uu____3478)::(t2,uu____3480)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3535 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3535
                 (fun r1  ->
                    let uu____3541 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3541
                      (fun b1  ->
                         let uu____3547 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3547
                           (fun t11  ->
                              let uu____3553 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3553
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3562)::(brs,uu____3564)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3599 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3599
                 (fun t2  ->
                    let uu____3605 =
                      let uu____3610 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3610 brs  in
                    FStar_Util.bind_opt uu____3605
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3629)::(t1,uu____3631)::(tacopt,uu____3633)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3678 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3678
                 (fun e1  ->
                    let uu____3684 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3684
                      (fun t2  ->
                         let uu____3690 =
                           let uu____3695 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3695 tacopt  in
                         FStar_Util.bind_opt uu____3690
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3714)::(c,uu____3716)::(tacopt,uu____3718)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3763 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3763
                 (fun e1  ->
                    let uu____3769 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3769
                      (fun c1  ->
                         let uu____3775 =
                           let uu____3780 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3780 tacopt  in
                         FStar_Util.bind_opt uu____3775
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
           | uu____3814 ->
               (if w
                then
                  (let uu____3828 =
                     let uu____3833 =
                       let uu____3834 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3834
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3833)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3828)
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
    let uu____3859 =
      let uu____3864 =
        let uu____3865 =
          let uu____3874 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3874  in
        let uu____3875 =
          let uu____3886 =
            let uu____3895 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3895  in
          let uu____3896 =
            let uu____3907 =
              let uu____3916 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____3916  in
            [uu____3907]  in
          uu____3886 :: uu____3896  in
        uu____3865 :: uu____3875  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3864
       in
    uu____3859 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3967 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3967 with
    | (hd1,args) ->
        let uu____4012 =
          let uu____4025 =
            let uu____4026 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4026.FStar_Syntax_Syntax.n  in
          (uu____4025, args)  in
        (match uu____4012 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4041)::(idx,uu____4043)::(s,uu____4045)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4090 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4090
               (fun nm1  ->
                  let uu____4096 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4096
                    (fun idx1  ->
                       let uu____4102 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4102
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4109 ->
             (if w
              then
                (let uu____4123 =
                   let uu____4128 =
                     let uu____4129 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4129
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4128)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4123)
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
        let uu____4150 =
          let uu____4155 =
            let uu____4156 =
              let uu____4165 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4165  in
            let uu____4166 =
              let uu____4177 =
                let uu____4186 =
                  let uu____4187 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4187 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4186  in
              [uu____4177]  in
            uu____4156 :: uu____4166  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4155
           in
        uu____4150 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4225 =
          let uu____4230 =
            let uu____4231 =
              let uu____4240 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4240  in
            let uu____4241 =
              let uu____4252 =
                let uu____4261 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4261  in
              [uu____4252]  in
            uu____4231 :: uu____4241  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4230
           in
        uu____4225 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___232_4288 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___232_4288.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___232_4288.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4305 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4305 with
    | (hd1,args) ->
        let uu____4350 =
          let uu____4363 =
            let uu____4364 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4364.FStar_Syntax_Syntax.n  in
          (uu____4363, args)  in
        (match uu____4350 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4379)::(md,uu____4381)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4416 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4416
               (fun t3  ->
                  let uu____4422 =
                    let uu____4427 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4427 md  in
                  FStar_Util.bind_opt uu____4422
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4446)::(post,uu____4448)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4483 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4483
               (fun pre1  ->
                  let uu____4489 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4489
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
         | uu____4513 ->
             (if w
              then
                (let uu____4527 =
                   let uu____4532 =
                     let uu____4533 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4533
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4532)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4527)
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
    let uu___233_4553 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___233_4553.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___233_4553.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4572 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4572 with
    | (hd1,args) ->
        let uu____4617 =
          let uu____4632 =
            let uu____4633 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4633.FStar_Syntax_Syntax.n  in
          (uu____4632, args)  in
        (match uu____4617 with
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
         | uu____4705 ->
             (if w
              then
                (let uu____4721 =
                   let uu____4726 =
                     let uu____4727 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4727
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4726)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4721)
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
    let uu____4757 =
      let uu____4758 = FStar_Syntax_Subst.compress t  in
      uu____4758.FStar_Syntax_Syntax.n  in
    match uu____4757 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____4764;
          FStar_Syntax_Syntax.rng = uu____4765;_}
        ->
        let uu____4768 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4768
    | uu____4769 ->
        (if w
         then
           (let uu____4771 =
              let uu____4776 =
                let uu____4777 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4777
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4776)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4771)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____4830 uu____4831 =
    let uu____4853 =
      let uu____4858 = FStar_Ident.range_of_id i  in
      let uu____4859 = FStar_Ident.text_of_id i  in (uu____4858, uu____4859)
       in
    embed repr rng uu____4853  in
  let unembed_ident t w uu____4883 =
    let uu____4888 = unembed' w repr t  in
    match uu____4888 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4907 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4907
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____4912 =
    FStar_Syntax_Syntax.t_tuple2_of FStar_Syntax_Syntax.t_range
      FStar_Syntax_Syntax.t_string
     in
  let uu____4913 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident uu____4912
    FStar_Ident.text_of_id uu____4913
  
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
        let uu____4946 =
          let uu____4951 =
            let uu____4952 =
              let uu____4961 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____4961  in
            let uu____4962 =
              let uu____4973 =
                let uu____4982 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____4982  in
              let uu____4983 =
                let uu____4994 =
                  let uu____5003 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5003  in
                let uu____5006 =
                  let uu____5017 =
                    let uu____5026 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5026  in
                  let uu____5027 =
                    let uu____5038 =
                      let uu____5047 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5047  in
                    [uu____5038]  in
                  uu____5017 :: uu____5027  in
                uu____4994 :: uu____5006  in
              uu____4973 :: uu____4983  in
            uu____4952 :: uu____4962  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4951
           in
        uu____4946 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5100 =
          let uu____5105 =
            let uu____5106 =
              let uu____5115 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5115  in
            let uu____5118 =
              let uu____5129 =
                let uu____5138 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5138  in
              [uu____5129]  in
            uu____5106 :: uu____5118  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5105
           in
        uu____5100 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5182 =
          let uu____5187 =
            let uu____5188 =
              let uu____5197 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5197  in
            let uu____5200 =
              let uu____5211 =
                let uu____5220 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5220  in
              let uu____5223 =
                let uu____5234 =
                  let uu____5243 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5243  in
                let uu____5244 =
                  let uu____5255 =
                    let uu____5264 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5264  in
                  let uu____5265 =
                    let uu____5276 =
                      let uu____5285 =
                        let uu____5286 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5286 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5285  in
                    [uu____5276]  in
                  uu____5255 :: uu____5265  in
                uu____5234 :: uu____5244  in
              uu____5211 :: uu____5223  in
            uu____5188 :: uu____5200  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5187
           in
        uu____5182 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___234_5349 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___234_5349.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___234_5349.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5366 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5366 with
    | (hd1,args) ->
        let uu____5411 =
          let uu____5424 =
            let uu____5425 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5425.FStar_Syntax_Syntax.n  in
          (uu____5424, args)  in
        (match uu____5411 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5440)::(us,uu____5442)::(bs,uu____5444)::(t2,uu____5446)::
            (dcs,uu____5448)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5513 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5513
               (fun nm1  ->
                  let uu____5527 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5527
                    (fun us1  ->
                       let uu____5541 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5541
                         (fun bs1  ->
                            let uu____5547 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5547
                              (fun t3  ->
                                 let uu____5553 =
                                   let uu____5560 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5560 dcs  in
                                 FStar_Util.bind_opt uu____5553
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_42  ->
                                           FStar_Pervasives_Native.Some _0_42)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5593)::(fvar1,uu____5595)::(univs1,uu____5597)::
            (ty,uu____5599)::(t2,uu____5601)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5666 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5666
               (fun r1  ->
                  let uu____5672 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5672
                    (fun fvar2  ->
                       let uu____5678 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5678
                         (fun univs2  ->
                            let uu____5692 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____5692
                              (fun ty1  ->
                                 let uu____5698 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____5698
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
         | uu____5722 ->
             (if w
              then
                (let uu____5736 =
                   let uu____5741 =
                     let uu____5742 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5742
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5741)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5736)
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
          let uu____5763 =
            let uu____5768 =
              let uu____5769 =
                let uu____5778 =
                  let uu____5779 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5779  in
                FStar_Syntax_Syntax.as_arg uu____5778  in
              [uu____5769]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5768
             in
          uu____5763 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5800 =
            let uu____5805 =
              let uu____5806 =
                let uu____5815 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5815  in
              let uu____5816 =
                let uu____5827 =
                  let uu____5836 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5836  in
                [uu____5827]  in
              uu____5806 :: uu____5816  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5805
             in
          uu____5800 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___235_5863 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___235_5863.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___235_5863.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5882 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5882 with
    | (hd1,args) ->
        let uu____5927 =
          let uu____5940 =
            let uu____5941 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5941.FStar_Syntax_Syntax.n  in
          (uu____5940, args)  in
        (match uu____5927 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5971)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5996 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____5996
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6005)::(e2,uu____6007)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6042 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6042
               (fun e11  ->
                  let uu____6048 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6048
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6055 ->
             (if w
              then
                (let uu____6069 =
                   let uu____6074 =
                     let uu____6075 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6075
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6074)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6069)
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
    let uu____6091 =
      let uu____6096 =
        let uu____6097 =
          let uu____6106 =
            let uu____6107 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____6107  in
          FStar_Syntax_Syntax.as_arg uu____6106  in
        [uu____6097]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____6096
       in
    uu____6091 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6132 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____6132 with
    | (bv,aq) ->
        let uu____6139 =
          let uu____6144 =
            let uu____6145 =
              let uu____6154 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____6154  in
            let uu____6155 =
              let uu____6166 =
                let uu____6175 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____6175  in
              [uu____6166]  in
            uu____6145 :: uu____6155  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____6144
           in
        uu____6139 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6208 =
      let uu____6213 =
        let uu____6214 =
          let uu____6223 =
            let uu____6224 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____6229 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____6224 i.FStar_Syntax_Syntax.rng uu____6229  in
          FStar_Syntax_Syntax.as_arg uu____6223  in
        [uu____6214]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____6213
       in
    uu____6208 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6258 =
      let uu____6263 =
        let uu____6264 =
          let uu____6273 =
            let uu____6274 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____6274  in
          FStar_Syntax_Syntax.as_arg uu____6273  in
        [uu____6264]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____6263
       in
    uu____6258 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6304 =
      let uu____6309 =
        let uu____6310 =
          let uu____6319 =
            let uu____6320 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____6320  in
          FStar_Syntax_Syntax.as_arg uu____6319  in
        [uu____6310]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6309
       in
    uu____6304 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  