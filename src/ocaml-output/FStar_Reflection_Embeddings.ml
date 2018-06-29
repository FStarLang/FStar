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
let (e_aqualv :
  FStar_Reflection_Data.aqualv FStar_Syntax_Embeddings.embedding) =
  let embed_aqualv rng q =
    let r =
      match q with
      | FStar_Reflection_Data.Q_Explicit  ->
          FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Q_Implicit  ->
          FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.t
       in
    let uu___225_514 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___225_514.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___225_514.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____533 = FStar_Syntax_Util.head_and_args t1  in
    match uu____533 with
    | (hd1,args) ->
        let uu____578 =
          let uu____593 =
            let uu____594 = FStar_Syntax_Util.un_uinst hd1  in
            uu____594.FStar_Syntax_Syntax.n  in
          (uu____593, args)  in
        (match uu____578 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____647 ->
             (if w
              then
                (let uu____663 =
                   let uu____668 =
                     let uu____669 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____669
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____668)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____663)
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
    let uu____701 =
      let uu____702 = FStar_Syntax_Subst.compress t  in
      uu____702.FStar_Syntax_Syntax.n  in
    match uu____701 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____708;
          FStar_Syntax_Syntax.rng = uu____709;_}
        ->
        let uu____712 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____712
    | uu____713 ->
        (if w
         then
           (let uu____715 =
              let uu____720 =
                let uu____721 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____721  in
              (FStar_Errors.Warning_NotEmbedded, uu____720)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____715)
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
    let uu____751 =
      let uu____752 = FStar_Syntax_Subst.compress t  in
      uu____752.FStar_Syntax_Syntax.n  in
    match uu____751 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____758;
          FStar_Syntax_Syntax.rng = uu____759;_}
        ->
        let uu____762 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____762
    | uu____763 ->
        (if w
         then
           (let uu____765 =
              let uu____770 =
                let uu____771 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____771  in
              (FStar_Errors.Warning_NotEmbedded, uu____770)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____765)
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
    let uu____801 =
      let uu____802 = FStar_Syntax_Subst.compress t  in
      uu____802.FStar_Syntax_Syntax.n  in
    match uu____801 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____808;
          FStar_Syntax_Syntax.rng = uu____809;_}
        ->
        let uu____812 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____812
    | uu____813 ->
        (if w
         then
           (let uu____815 =
              let uu____820 =
                let uu____821 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____821  in
              (FStar_Errors.Warning_NotEmbedded, uu____820)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____815)
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
          let uu____842 =
            let uu____847 =
              let uu____848 =
                let uu____857 =
                  let uu____858 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____858  in
                FStar_Syntax_Syntax.as_arg uu____857  in
              [uu____848]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____847
             in
          uu____842 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____878 =
            let uu____883 =
              let uu____884 =
                let uu____893 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____893  in
              [uu____884]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____883
             in
          uu____878 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___226_912 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___226_912.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___226_912.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____931 = FStar_Syntax_Util.head_and_args t1  in
    match uu____931 with
    | (hd1,args) ->
        let uu____976 =
          let uu____991 =
            let uu____992 = FStar_Syntax_Util.un_uinst hd1  in
            uu____992.FStar_Syntax_Syntax.n  in
          (uu____991, args)  in
        (match uu____976 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1066)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1101 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1101
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1110)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1145 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1145
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1152 ->
             (if w
              then
                (let uu____1168 =
                   let uu____1173 =
                     let uu____1174 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1174
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1173)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1168)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1182  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1195 =
            let uu____1200 =
              let uu____1201 =
                let uu____1210 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1210  in
              [uu____1201]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1200
             in
          uu____1195 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1235 =
            let uu____1240 =
              let uu____1241 =
                let uu____1250 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1250  in
              let uu____1251 =
                let uu____1262 =
                  let uu____1271 =
                    let uu____1272 =
                      let uu____1277 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1277  in
                    embed uu____1272 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1271  in
                [uu____1262]  in
              uu____1241 :: uu____1251  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1240
             in
          uu____1235 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1309 =
            let uu____1314 =
              let uu____1315 =
                let uu____1324 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1324  in
              [uu____1315]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1314
             in
          uu____1309 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1344 =
            let uu____1349 =
              let uu____1350 =
                let uu____1359 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1359  in
              [uu____1350]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1349
             in
          uu____1344 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1380 =
            let uu____1385 =
              let uu____1386 =
                let uu____1395 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1395  in
              let uu____1396 =
                let uu____1407 =
                  let uu____1416 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1416  in
                [uu____1407]  in
              uu____1386 :: uu____1396  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1385
             in
          uu____1380 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1459 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1459 with
      | (hd1,args) ->
          let uu____1504 =
            let uu____1517 =
              let uu____1518 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1518.FStar_Syntax_Syntax.n  in
            (uu____1517, args)  in
          (match uu____1504 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1533)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1558 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1558
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1567)::(ps,uu____1569)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1604 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1604
                 (fun f1  ->
                    let uu____1610 =
                      let uu____1615 =
                        let uu____1620 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1620  in
                      unembed' w uu____1615 ps  in
                    FStar_Util.bind_opt uu____1610
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1637)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1662 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1662
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1671)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1696 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1696
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1705)::(t2,uu____1707)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1742 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1742
                 (fun bv1  ->
                    let uu____1748 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1748
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1755 ->
               (if w
                then
                  (let uu____1769 =
                     let uu____1774 =
                       let uu____1775 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1775
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1774)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1769)
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
    let uu____1794 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1794
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1808 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1808 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1830 =
            let uu____1835 =
              let uu____1836 =
                let uu____1845 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1845  in
              [uu____1836]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1835
             in
          uu____1830 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1865 =
            let uu____1870 =
              let uu____1871 =
                let uu____1880 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1880  in
              [uu____1871]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1870
             in
          uu____1865 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1900 =
            let uu____1905 =
              let uu____1906 =
                let uu____1915 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1915  in
              [uu____1906]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1905
             in
          uu____1900 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1936 =
            let uu____1941 =
              let uu____1942 =
                let uu____1951 =
                  let uu____1952 = e_term_aq aq  in embed uu____1952 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____1951  in
              let uu____1955 =
                let uu____1966 =
                  let uu____1975 =
                    let uu____1976 = e_argv_aq aq  in embed uu____1976 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____1975  in
                [uu____1966]  in
              uu____1942 :: uu____1955  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1941
             in
          uu____1936 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2015 =
            let uu____2020 =
              let uu____2021 =
                let uu____2030 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2030  in
              let uu____2031 =
                let uu____2042 =
                  let uu____2051 =
                    let uu____2052 = e_term_aq aq  in embed uu____2052 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2051  in
                [uu____2042]  in
              uu____2021 :: uu____2031  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2020
             in
          uu____2015 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2083 =
            let uu____2088 =
              let uu____2089 =
                let uu____2098 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2098  in
              let uu____2099 =
                let uu____2110 =
                  let uu____2119 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2119  in
                [uu____2110]  in
              uu____2089 :: uu____2099  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2088
             in
          uu____2083 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2147 =
            let uu____2152 =
              let uu____2153 =
                let uu____2162 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2162  in
              [uu____2153]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2152
             in
          uu____2147 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2183 =
            let uu____2188 =
              let uu____2189 =
                let uu____2198 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2198  in
              let uu____2199 =
                let uu____2210 =
                  let uu____2219 =
                    let uu____2220 = e_term_aq aq  in embed uu____2220 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2219  in
                [uu____2210]  in
              uu____2189 :: uu____2199  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2188
             in
          uu____2183 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2250 =
            let uu____2255 =
              let uu____2256 =
                let uu____2265 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2265  in
              [uu____2256]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2255
             in
          uu____2250 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2286 =
            let uu____2291 =
              let uu____2292 =
                let uu____2301 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2301  in
              let uu____2302 =
                let uu____2313 =
                  let uu____2322 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2322  in
                [uu____2313]  in
              uu____2292 :: uu____2302  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2291
             in
          uu____2286 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2357 =
            let uu____2362 =
              let uu____2363 =
                let uu____2372 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2372  in
              let uu____2373 =
                let uu____2384 =
                  let uu____2393 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2393  in
                let uu____2394 =
                  let uu____2405 =
                    let uu____2414 =
                      let uu____2415 = e_term_aq aq  in
                      embed uu____2415 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2414  in
                  let uu____2418 =
                    let uu____2429 =
                      let uu____2438 =
                        let uu____2439 = e_term_aq aq  in
                        embed uu____2439 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2438  in
                    [uu____2429]  in
                  uu____2405 :: uu____2418  in
                uu____2384 :: uu____2394  in
              uu____2363 :: uu____2373  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2362
             in
          uu____2357 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2490 =
            let uu____2495 =
              let uu____2496 =
                let uu____2505 =
                  let uu____2506 = e_term_aq aq  in embed uu____2506 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2505  in
              let uu____2509 =
                let uu____2520 =
                  let uu____2529 =
                    let uu____2530 =
                      let uu____2539 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2539  in
                    embed uu____2530 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2529  in
                [uu____2520]  in
              uu____2496 :: uu____2509  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2495
             in
          uu____2490 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2589 =
            let uu____2594 =
              let uu____2595 =
                let uu____2604 =
                  let uu____2605 = e_term_aq aq  in embed uu____2605 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2604  in
              let uu____2608 =
                let uu____2619 =
                  let uu____2628 =
                    let uu____2629 = e_term_aq aq  in embed uu____2629 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2628  in
                let uu____2632 =
                  let uu____2643 =
                    let uu____2652 =
                      let uu____2653 =
                        let uu____2658 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2658  in
                      embed uu____2653 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2652  in
                  [uu____2643]  in
                uu____2619 :: uu____2632  in
              uu____2595 :: uu____2608  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2594
             in
          uu____2589 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2704 =
            let uu____2709 =
              let uu____2710 =
                let uu____2719 =
                  let uu____2720 = e_term_aq aq  in embed uu____2720 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2719  in
              let uu____2723 =
                let uu____2734 =
                  let uu____2743 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2743  in
                let uu____2744 =
                  let uu____2755 =
                    let uu____2764 =
                      let uu____2765 =
                        let uu____2770 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2770  in
                      embed uu____2765 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2764  in
                  [uu____2755]  in
                uu____2734 :: uu____2744  in
              uu____2710 :: uu____2723  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2709
             in
          uu____2704 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___227_2809 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___227_2809.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___227_2809.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2825 = FStar_Syntax_Util.head_and_args t  in
      match uu____2825 with
      | (hd1,args) ->
          let uu____2870 =
            let uu____2883 =
              let uu____2884 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2884.FStar_Syntax_Syntax.n  in
            (uu____2883, args)  in
          (match uu____2870 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2899)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2924 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2924
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2933)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____2958 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2958
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____2967)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____2992 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____2992
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3001)::(r,uu____3003)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3038 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3038
                 (fun l1  ->
                    let uu____3044 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3044
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3053)::(t1,uu____3055)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3090 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3090
                 (fun b1  ->
                    let uu____3096 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3096
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3105)::(t1,uu____3107)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3142 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3142
                 (fun b1  ->
                    let uu____3148 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3148
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3157)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3182 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3182
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3191)::(t1,uu____3193)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3228 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3228
                 (fun b1  ->
                    let uu____3234 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3234
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3243)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3268 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3268
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3277)::(l,uu____3279)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3314 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3314
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3325)::(b,uu____3327)::(t1,uu____3329)::(t2,uu____3331)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3386 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3386
                 (fun r1  ->
                    let uu____3392 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3392
                      (fun b1  ->
                         let uu____3398 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3398
                           (fun t11  ->
                              let uu____3404 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3404
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3413)::(brs,uu____3415)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3450 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3450
                 (fun t2  ->
                    let uu____3456 =
                      let uu____3461 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3461 brs  in
                    FStar_Util.bind_opt uu____3456
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3480)::(t1,uu____3482)::(tacopt,uu____3484)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3529 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3529
                 (fun e1  ->
                    let uu____3535 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3535
                      (fun t2  ->
                         let uu____3541 =
                           let uu____3546 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3546 tacopt  in
                         FStar_Util.bind_opt uu____3541
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3565)::(c,uu____3567)::(tacopt,uu____3569)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3614 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3614
                 (fun e1  ->
                    let uu____3620 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3620
                      (fun c1  ->
                         let uu____3626 =
                           let uu____3631 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3631 tacopt  in
                         FStar_Util.bind_opt uu____3626
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
           | uu____3665 ->
               (if w
                then
                  (let uu____3679 =
                     let uu____3684 =
                       let uu____3685 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3685
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3684)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3679)
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
    let uu____3710 =
      let uu____3715 =
        let uu____3716 =
          let uu____3725 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3725  in
        let uu____3726 =
          let uu____3737 =
            let uu____3746 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3746  in
          let uu____3747 =
            let uu____3758 =
              let uu____3767 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____3767  in
            [uu____3758]  in
          uu____3737 :: uu____3747  in
        uu____3716 :: uu____3726  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3715
       in
    uu____3710 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3818 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3818 with
    | (hd1,args) ->
        let uu____3863 =
          let uu____3876 =
            let uu____3877 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3877.FStar_Syntax_Syntax.n  in
          (uu____3876, args)  in
        (match uu____3863 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3892)::(idx,uu____3894)::(s,uu____3896)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____3941 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____3941
               (fun nm1  ->
                  let uu____3947 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____3947
                    (fun idx1  ->
                       let uu____3953 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____3953
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____3960 ->
             (if w
              then
                (let uu____3974 =
                   let uu____3979 =
                     let uu____3980 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____3980
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3979)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3974)
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
        let uu____4001 =
          let uu____4006 =
            let uu____4007 =
              let uu____4016 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4016  in
            let uu____4017 =
              let uu____4028 =
                let uu____4037 =
                  let uu____4038 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4038 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4037  in
              [uu____4028]  in
            uu____4007 :: uu____4017  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4006
           in
        uu____4001 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4076 =
          let uu____4081 =
            let uu____4082 =
              let uu____4091 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4091  in
            let uu____4092 =
              let uu____4103 =
                let uu____4112 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4112  in
              [uu____4103]  in
            uu____4082 :: uu____4092  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4081
           in
        uu____4076 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___228_4139 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___228_4139.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___228_4139.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4156 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4156 with
    | (hd1,args) ->
        let uu____4201 =
          let uu____4214 =
            let uu____4215 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4215.FStar_Syntax_Syntax.n  in
          (uu____4214, args)  in
        (match uu____4201 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4230)::(md,uu____4232)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4267 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4267
               (fun t3  ->
                  let uu____4273 =
                    let uu____4278 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4278 md  in
                  FStar_Util.bind_opt uu____4273
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4297)::(post,uu____4299)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4334 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4334
               (fun pre1  ->
                  let uu____4340 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4340
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
         | uu____4364 ->
             (if w
              then
                (let uu____4378 =
                   let uu____4383 =
                     let uu____4384 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4384
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4383)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4378)
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
    let uu___229_4404 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___229_4404.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___229_4404.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4423 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4423 with
    | (hd1,args) ->
        let uu____4468 =
          let uu____4483 =
            let uu____4484 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4484.FStar_Syntax_Syntax.n  in
          (uu____4483, args)  in
        (match uu____4468 with
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
         | uu____4556 ->
             (if w
              then
                (let uu____4572 =
                   let uu____4577 =
                     let uu____4578 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4578
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4577)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4572)
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
    let uu____4608 =
      let uu____4609 = FStar_Syntax_Subst.compress t  in
      uu____4609.FStar_Syntax_Syntax.n  in
    match uu____4608 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____4615;
          FStar_Syntax_Syntax.rng = uu____4616;_}
        ->
        let uu____4619 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4619
    | uu____4620 ->
        (if w
         then
           (let uu____4622 =
              let uu____4627 =
                let uu____4628 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4628
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4627)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4622)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,ty,t) ->
        let uu____4647 =
          let uu____4652 =
            let uu____4653 =
              let uu____4662 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____4662  in
            let uu____4663 =
              let uu____4674 =
                let uu____4683 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____4683  in
              let uu____4684 =
                let uu____4695 =
                  let uu____4704 = embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____4704  in
                let uu____4705 =
                  let uu____4716 =
                    let uu____4725 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____4725  in
                  [uu____4716]  in
                uu____4695 :: uu____4705  in
              uu____4674 :: uu____4684  in
            uu____4653 :: uu____4663  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4652
           in
        uu____4647 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4770 =
          let uu____4775 =
            let uu____4776 =
              let uu____4785 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____4785  in
            let uu____4788 =
              let uu____4799 =
                let uu____4808 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____4808  in
              [uu____4799]  in
            uu____4776 :: uu____4788  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____4775
           in
        uu____4770 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____4847 =
          let uu____4852 =
            let uu____4853 =
              let uu____4862 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____4862  in
            let uu____4865 =
              let uu____4876 =
                let uu____4885 = embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____4885  in
              let uu____4886 =
                let uu____4897 =
                  let uu____4906 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____4906  in
                let uu____4907 =
                  let uu____4918 =
                    let uu____4927 =
                      let uu____4928 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      embed uu____4928 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____4927  in
                  [uu____4918]  in
                uu____4897 :: uu____4907  in
              uu____4876 :: uu____4886  in
            uu____4853 :: uu____4865  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____4852
           in
        uu____4847 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___230_4983 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___230_4983.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___230_4983.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5000 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5000 with
    | (hd1,args) ->
        let uu____5045 =
          let uu____5058 =
            let uu____5059 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5059.FStar_Syntax_Syntax.n  in
          (uu____5058, args)  in
        (match uu____5045 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5074)::(bs,uu____5076)::(t2,uu____5078)::(dcs,uu____5080)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5135 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5135
               (fun nm1  ->
                  let uu____5149 = unembed' w e_binders bs  in
                  FStar_Util.bind_opt uu____5149
                    (fun bs1  ->
                       let uu____5155 = unembed' w e_term t2  in
                       FStar_Util.bind_opt uu____5155
                         (fun t3  ->
                            let uu____5161 =
                              let uu____5168 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_string_list
                                 in
                              unembed' w uu____5168 dcs  in
                            FStar_Util.bind_opt uu____5161
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_42  ->
                                      FStar_Pervasives_Native.Some _0_42)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5199)::(fvar1,uu____5201)::(ty,uu____5203)::(t2,uu____5205)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5260 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5260
               (fun r1  ->
                  let uu____5266 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5266
                    (fun fvar2  ->
                       let uu____5272 = unembed' w e_term ty  in
                       FStar_Util.bind_opt uu____5272
                         (fun ty1  ->
                            let uu____5278 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5278
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_43  ->
                                      FStar_Pervasives_Native.Some _0_43)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____5300 ->
             (if w
              then
                (let uu____5314 =
                   let uu____5319 =
                     let uu____5320 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5320
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5319)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5314)
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
          let uu____5341 =
            let uu____5346 =
              let uu____5347 =
                let uu____5356 =
                  let uu____5357 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5357  in
                FStar_Syntax_Syntax.as_arg uu____5356  in
              [uu____5347]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5346
             in
          uu____5341 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5378 =
            let uu____5383 =
              let uu____5384 =
                let uu____5393 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5393  in
              let uu____5394 =
                let uu____5405 =
                  let uu____5414 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5414  in
                [uu____5405]  in
              uu____5384 :: uu____5394  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5383
             in
          uu____5378 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___231_5441 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___231_5441.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___231_5441.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5460 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5460 with
    | (hd1,args) ->
        let uu____5505 =
          let uu____5518 =
            let uu____5519 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5519.FStar_Syntax_Syntax.n  in
          (uu____5518, args)  in
        (match uu____5505 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5549)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5574 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____5574
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____5583)::(e2,uu____5585)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____5620 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____5620
               (fun e11  ->
                  let uu____5626 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____5626
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____5633 ->
             (if w
              then
                (let uu____5647 =
                   let uu____5652 =
                     let uu____5653 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____5653
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5652)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5647)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp 
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5663 =
      let uu____5668 =
        let uu____5669 =
          let uu____5678 =
            let uu____5679 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____5679  in
          FStar_Syntax_Syntax.as_arg uu____5678  in
        [uu____5669]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____5668
       in
    uu____5663 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5704 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____5704 with
    | (bv,aq) ->
        let uu____5711 =
          let uu____5716 =
            let uu____5717 =
              let uu____5726 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____5726  in
            let uu____5727 =
              let uu____5738 =
                let uu____5747 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____5747  in
              [uu____5738]  in
            uu____5717 :: uu____5727  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____5716
           in
        uu____5711 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5780 =
      let uu____5785 =
        let uu____5786 =
          let uu____5795 =
            let uu____5796 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____5801 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____5796 i.FStar_Syntax_Syntax.rng uu____5801  in
          FStar_Syntax_Syntax.as_arg uu____5795  in
        [uu____5786]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____5785
       in
    uu____5780 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5830 =
      let uu____5835 =
        let uu____5836 =
          let uu____5845 =
            let uu____5846 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____5846  in
          FStar_Syntax_Syntax.as_arg uu____5845  in
        [uu____5836]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____5835
       in
    uu____5830 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5876 =
      let uu____5881 =
        let uu____5882 =
          let uu____5891 =
            let uu____5892 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____5892  in
          FStar_Syntax_Syntax.as_arg uu____5891  in
        [uu____5882]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____5881
       in
    uu____5876 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  