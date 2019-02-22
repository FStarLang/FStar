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
        let uu____53 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____53
  
let embed :
  'Auu____101 .
    'Auu____101 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____101 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____121 = FStar_Syntax_Embeddings.embed e x  in
        uu____121 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____162 .
    Prims.bool ->
      'Auu____162 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____162 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____186 = FStar_Syntax_Embeddings.unembed e x  in
        uu____186 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____228 =
      let uu____229 = FStar_Syntax_Subst.compress t  in
      uu____229.FStar_Syntax_Syntax.n  in
    match uu____228 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____235;
          FStar_Syntax_Syntax.rng = uu____236;_}
        ->
        let uu____239 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____239
    | uu____240 ->
        (if w
         then
           (let uu____243 =
              let uu____249 =
                let uu____251 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____251  in
              (FStar_Errors.Warning_NotEmbedded, uu____249)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____243)
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
    let uu____288 =
      let uu____289 = FStar_Syntax_Subst.compress t  in
      uu____289.FStar_Syntax_Syntax.n  in
    match uu____288 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____295;
          FStar_Syntax_Syntax.rng = uu____296;_}
        ->
        let uu____299 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____299
    | uu____300 ->
        (if w
         then
           (let uu____303 =
              let uu____309 =
                let uu____311 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____311  in
              (FStar_Errors.Warning_NotEmbedded, uu____309)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____303)
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
          let uu____363 = f x  in
          FStar_Util.bind_opt uu____363
            (fun x1  ->
               let uu____371 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____371
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
        let uu____440 =
          mapM_opt
            (fun uu____453  ->
               match uu____453 with
               | (bv,e) ->
                   let uu____462 = unembed_term w e  in
                   FStar_Util.bind_opt uu____462
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____440
          (fun s  ->
             let uu____476 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____476)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____478 =
        let uu____479 = FStar_Syntax_Subst.compress t1  in
        uu____479.FStar_Syntax_Syntax.n  in
      match uu____478 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____490 ->
          (if w
           then
             (let uu____493 =
                let uu____499 =
                  let uu____501 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____501  in
                (FStar_Errors.Warning_NotEmbedded, uu____499)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____493)
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
          let uu____536 =
            let uu____541 =
              let uu____542 =
                let uu____551 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____551  in
              [uu____542]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____541
             in
          uu____536 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___13_570 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___13_570.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___13_570.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____591 = FStar_Syntax_Util.head_and_args t1  in
    match uu____591 with
    | (hd1,args) ->
        let uu____636 =
          let uu____651 =
            let uu____652 = FStar_Syntax_Util.un_uinst hd1  in
            uu____652.FStar_Syntax_Syntax.n  in
          (uu____651, args)  in
        (match uu____636 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____707)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____742 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____742
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____747 ->
             (if w
              then
                (let uu____764 =
                   let uu____770 =
                     let uu____772 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____772
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____770)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____764)
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
    let uu____812 =
      let uu____813 = FStar_Syntax_Subst.compress t  in
      uu____813.FStar_Syntax_Syntax.n  in
    match uu____812 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____819;
          FStar_Syntax_Syntax.rng = uu____820;_}
        ->
        let uu____823 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____823
    | uu____824 ->
        (if w
         then
           (let uu____827 =
              let uu____833 =
                let uu____835 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____835  in
              (FStar_Errors.Warning_NotEmbedded, uu____833)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____827)
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
    let uu____872 =
      let uu____873 = FStar_Syntax_Subst.compress t  in
      uu____873.FStar_Syntax_Syntax.n  in
    match uu____872 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____879;
          FStar_Syntax_Syntax.rng = uu____880;_}
        ->
        let uu____883 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____883
    | uu____884 ->
        (if w
         then
           (let uu____887 =
              let uu____893 =
                let uu____895 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____895  in
              (FStar_Errors.Warning_NotEmbedded, uu____893)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____887)
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
    let uu____932 =
      let uu____933 = FStar_Syntax_Subst.compress t  in
      uu____933.FStar_Syntax_Syntax.n  in
    match uu____932 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____939;
          FStar_Syntax_Syntax.rng = uu____940;_}
        ->
        let uu____943 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____943
    | uu____944 ->
        (if w
         then
           (let uu____947 =
              let uu____953 =
                let uu____955 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____955  in
              (FStar_Errors.Warning_NotEmbedded, uu____953)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____947)
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
          let uu____981 =
            let uu____986 =
              let uu____987 =
                let uu____996 =
                  let uu____997 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____997  in
                FStar_Syntax_Syntax.as_arg uu____996  in
              [uu____987]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____986
             in
          uu____981 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____1019 =
            let uu____1024 =
              let uu____1025 =
                let uu____1034 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____1034  in
              [uu____1025]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____1024
             in
          uu____1019 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____1055 =
            let uu____1060 =
              let uu____1061 =
                let uu____1070 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1070  in
              [uu____1061]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____1060
             in
          uu____1055 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____1090 =
            let uu____1095 =
              let uu____1096 =
                let uu____1105 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____1105  in
              [uu____1096]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____1095
             in
          uu____1090 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___14_1127 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___14_1127.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___14_1127.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1148 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1148 with
    | (hd1,args) ->
        let uu____1193 =
          let uu____1208 =
            let uu____1209 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1209.FStar_Syntax_Syntax.n  in
          (uu____1208, args)  in
        (match uu____1193 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1283)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1318 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1318
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1327)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1362 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1362
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____1375)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1410 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____1410
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _0_3  -> FStar_Pervasives_Native.Some _0_3)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_4  -> FStar_Pervasives_Native.Some _0_4)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____1440)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____1475 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____1475
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _0_5  -> FStar_Pervasives_Native.Some _0_5)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____1494 ->
             (if w
              then
                (let uu____1511 =
                   let uu____1517 =
                     let uu____1519 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1519
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1517)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1511)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1532  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1545 =
            let uu____1550 =
              let uu____1551 =
                let uu____1560 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1560  in
              [uu____1551]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1550
             in
          uu____1545 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1585 =
            let uu____1590 =
              let uu____1591 =
                let uu____1600 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1600  in
              let uu____1601 =
                let uu____1612 =
                  let uu____1621 =
                    let uu____1622 =
                      let uu____1627 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1627  in
                    embed uu____1622 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1621  in
                [uu____1612]  in
              uu____1591 :: uu____1601  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1590
             in
          uu____1585 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1659 =
            let uu____1664 =
              let uu____1665 =
                let uu____1674 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1674  in
              [uu____1665]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1664
             in
          uu____1659 FStar_Pervasives_Native.None rng
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
          let uu____1730 =
            let uu____1735 =
              let uu____1736 =
                let uu____1745 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1745  in
              let uu____1746 =
                let uu____1757 =
                  let uu____1766 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1766  in
                [uu____1757]  in
              uu____1736 :: uu____1746  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1735
             in
          uu____1730 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1811 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1811 with
      | (hd1,args) ->
          let uu____1856 =
            let uu____1869 =
              let uu____1870 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1870.FStar_Syntax_Syntax.n  in
            (uu____1869, args)  in
          (match uu____1856 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1885)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1910 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1910
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_6  -> FStar_Pervasives_Native.Some _0_6)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1919)::(ps,uu____1921)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1956 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1956
                 (fun f1  ->
                    let uu____1962 =
                      let uu____1967 =
                        let uu____1972 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1972  in
                      unembed' w uu____1967 ps  in
                    FStar_Util.bind_opt uu____1962
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_7  -> FStar_Pervasives_Native.Some _0_7)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1989)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____2014 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2014
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_8  -> FStar_Pervasives_Native.Some _0_8)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2023)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____2048 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2048
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_9  -> FStar_Pervasives_Native.Some _0_9)
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
                           (fun _0_10  -> FStar_Pervasives_Native.Some _0_10)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2107 ->
               (if w
                then
                  (let uu____2122 =
                     let uu____2128 =
                       let uu____2130 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2130
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2128)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2122)
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
    let uu____2157 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2157
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2172 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2172 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2195 =
            let uu____2200 =
              let uu____2201 =
                let uu____2210 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2210  in
              [uu____2201]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____2200
             in
          uu____2195 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2230 =
            let uu____2235 =
              let uu____2236 =
                let uu____2245 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2245  in
              [uu____2236]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2235
             in
          uu____2230 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2265 =
            let uu____2270 =
              let uu____2271 =
                let uu____2280 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2280  in
              [uu____2271]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2270
             in
          uu____2265 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2301 =
            let uu____2306 =
              let uu____2307 =
                let uu____2316 =
                  let uu____2317 = e_term_aq aq  in embed uu____2317 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2316  in
              let uu____2320 =
                let uu____2331 =
                  let uu____2340 =
                    let uu____2341 = e_argv_aq aq  in embed uu____2341 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2340  in
                [uu____2331]  in
              uu____2307 :: uu____2320  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2306
             in
          uu____2301 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2380 =
            let uu____2385 =
              let uu____2386 =
                let uu____2395 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2395  in
              let uu____2396 =
                let uu____2407 =
                  let uu____2416 =
                    let uu____2417 = e_term_aq aq  in embed uu____2417 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2416  in
                [uu____2407]  in
              uu____2386 :: uu____2396  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2385
             in
          uu____2380 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2448 =
            let uu____2453 =
              let uu____2454 =
                let uu____2463 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2463  in
              let uu____2464 =
                let uu____2475 =
                  let uu____2484 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2484  in
                [uu____2475]  in
              uu____2454 :: uu____2464  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2453
             in
          uu____2448 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2512 =
            let uu____2517 =
              let uu____2518 =
                let uu____2527 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2527  in
              [uu____2518]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2517
             in
          uu____2512 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2548 =
            let uu____2553 =
              let uu____2554 =
                let uu____2563 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2563  in
              let uu____2564 =
                let uu____2575 =
                  let uu____2584 =
                    let uu____2585 = e_term_aq aq  in embed uu____2585 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2584  in
                [uu____2575]  in
              uu____2554 :: uu____2564  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2553
             in
          uu____2548 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2615 =
            let uu____2620 =
              let uu____2621 =
                let uu____2630 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2630  in
              [uu____2621]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2620
             in
          uu____2615 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2651 =
            let uu____2656 =
              let uu____2657 =
                let uu____2666 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2666  in
              let uu____2667 =
                let uu____2678 =
                  let uu____2687 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2687  in
                [uu____2678]  in
              uu____2657 :: uu____2667  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2656
             in
          uu____2651 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2724 =
            let uu____2729 =
              let uu____2730 =
                let uu____2739 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2739  in
              let uu____2741 =
                let uu____2752 =
                  let uu____2761 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2761  in
                let uu____2762 =
                  let uu____2773 =
                    let uu____2782 =
                      let uu____2783 = e_term_aq aq  in
                      embed uu____2783 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2782  in
                  let uu____2786 =
                    let uu____2797 =
                      let uu____2806 =
                        let uu____2807 = e_term_aq aq  in
                        embed uu____2807 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2806  in
                    [uu____2797]  in
                  uu____2773 :: uu____2786  in
                uu____2752 :: uu____2762  in
              uu____2730 :: uu____2741  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2729
             in
          uu____2724 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2858 =
            let uu____2863 =
              let uu____2864 =
                let uu____2873 =
                  let uu____2874 = e_term_aq aq  in embed uu____2874 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2873  in
              let uu____2877 =
                let uu____2888 =
                  let uu____2897 =
                    let uu____2898 =
                      let uu____2907 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2907  in
                    embed uu____2898 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2897  in
                [uu____2888]  in
              uu____2864 :: uu____2877  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2863
             in
          uu____2858 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2957 =
            let uu____2962 =
              let uu____2963 =
                let uu____2972 =
                  let uu____2973 = e_term_aq aq  in embed uu____2973 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2972  in
              let uu____2976 =
                let uu____2987 =
                  let uu____2996 =
                    let uu____2997 = e_term_aq aq  in embed uu____2997 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2996  in
                let uu____3000 =
                  let uu____3011 =
                    let uu____3020 =
                      let uu____3021 =
                        let uu____3026 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3026  in
                      embed uu____3021 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3020  in
                  [uu____3011]  in
                uu____2987 :: uu____3000  in
              uu____2963 :: uu____2976  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2962
             in
          uu____2957 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____3072 =
            let uu____3077 =
              let uu____3078 =
                let uu____3087 =
                  let uu____3088 = e_term_aq aq  in embed uu____3088 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3087  in
              let uu____3091 =
                let uu____3102 =
                  let uu____3111 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____3111  in
                let uu____3112 =
                  let uu____3123 =
                    let uu____3132 =
                      let uu____3133 =
                        let uu____3138 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3138  in
                      embed uu____3133 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3132  in
                  [uu____3123]  in
                uu____3102 :: uu____3112  in
              uu____3078 :: uu____3091  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____3077
             in
          uu____3072 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___15_3177 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___15_3177.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___15_3177.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3195 = FStar_Syntax_Util.head_and_args t  in
      match uu____3195 with
      | (hd1,args) ->
          let uu____3240 =
            let uu____3253 =
              let uu____3254 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3254.FStar_Syntax_Syntax.n  in
            (uu____3253, args)  in
          (match uu____3240 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3269)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3294 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3294
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_11  -> FStar_Pervasives_Native.Some _0_11)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3303)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3328 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3328
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_12  -> FStar_Pervasives_Native.Some _0_12)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3337)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3362 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3362
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_13  -> FStar_Pervasives_Native.Some _0_13)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3371)::(r,uu____3373)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3408 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3408
                 (fun l1  ->
                    let uu____3414 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3414
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3423)::(t1,uu____3425)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3460 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3460
                 (fun b1  ->
                    let uu____3466 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3466
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3475)::(t1,uu____3477)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3512 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3512
                 (fun b1  ->
                    let uu____3518 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3518
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3527)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3552 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3552
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3561)::(t1,uu____3563)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3598 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3598
                 (fun b1  ->
                    let uu____3604 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3604
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3613)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3638 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3638
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3647)::(l,uu____3649)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3684 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3684
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3695)::(b,uu____3697)::(t1,uu____3699)::(t2,uu____3701)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3756 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3756
                 (fun r1  ->
                    let uu____3766 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3766
                      (fun b1  ->
                         let uu____3772 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3772
                           (fun t11  ->
                              let uu____3778 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3778
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_21  ->
                                        FStar_Pervasives_Native.Some _0_21)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3788)::(brs,uu____3790)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3825 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3825
                 (fun t2  ->
                    let uu____3831 =
                      let uu____3836 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3836 brs  in
                    FStar_Util.bind_opt uu____3831
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3855)::(t1,uu____3857)::(tacopt,uu____3859)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3904 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3904
                 (fun e1  ->
                    let uu____3910 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3910
                      (fun t2  ->
                         let uu____3916 =
                           let uu____3921 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3921 tacopt  in
                         FStar_Util.bind_opt uu____3916
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_23  ->
                                   FStar_Pervasives_Native.Some _0_23)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3940)::(c,uu____3942)::(tacopt,uu____3944)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3989 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3989
                 (fun e1  ->
                    let uu____3995 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3995
                      (fun c1  ->
                         let uu____4001 =
                           let uu____4006 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4006 tacopt  in
                         FStar_Util.bind_opt uu____4001
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_24  ->
                                   FStar_Pervasives_Native.Some _0_24)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____4040 ->
               (if w
                then
                  (let uu____4055 =
                     let uu____4061 =
                       let uu____4063 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4063
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4061)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____4055)
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
    let uu____4092 =
      let uu____4097 =
        let uu____4098 =
          let uu____4107 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____4107  in
        let uu____4109 =
          let uu____4120 =
            let uu____4129 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4129  in
          let uu____4130 =
            let uu____4141 =
              let uu____4150 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4150  in
            [uu____4141]  in
          uu____4120 :: uu____4130  in
        uu____4098 :: uu____4109  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4097
       in
    uu____4092 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4203 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4203 with
    | (hd1,args) ->
        let uu____4248 =
          let uu____4261 =
            let uu____4262 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4262.FStar_Syntax_Syntax.n  in
          (uu____4261, args)  in
        (match uu____4248 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4277)::(idx,uu____4279)::(s,uu____4281)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4326 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4326
               (fun nm1  ->
                  let uu____4336 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4336
                    (fun idx1  ->
                       let uu____4342 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4342
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_26  ->
                                 FStar_Pervasives_Native.Some _0_26)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4349 ->
             (if w
              then
                (let uu____4364 =
                   let uu____4370 =
                     let uu____4372 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4372
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4370)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4364)
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
        let uu____4398 =
          let uu____4403 =
            let uu____4404 =
              let uu____4413 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4413  in
            let uu____4414 =
              let uu____4425 =
                let uu____4434 =
                  let uu____4435 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4435 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4434  in
              [uu____4425]  in
            uu____4404 :: uu____4414  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4403
           in
        uu____4398 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4473 =
          let uu____4478 =
            let uu____4479 =
              let uu____4488 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4488  in
            let uu____4489 =
              let uu____4500 =
                let uu____4509 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4509  in
              [uu____4500]  in
            uu____4479 :: uu____4489  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4478
           in
        uu____4473 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___16_4536 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___16_4536.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___16_4536.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4555 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4555 with
    | (hd1,args) ->
        let uu____4600 =
          let uu____4613 =
            let uu____4614 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4614.FStar_Syntax_Syntax.n  in
          (uu____4613, args)  in
        (match uu____4600 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4629)::(md,uu____4631)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4666 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4666
               (fun t3  ->
                  let uu____4672 =
                    let uu____4677 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4677 md  in
                  FStar_Util.bind_opt uu____4672
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4696)::(post,uu____4698)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4733 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4733
               (fun pre1  ->
                  let uu____4739 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4739
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
               FStar_Reflection_Data.C_Unknown
         | uu____4763 ->
             (if w
              then
                (let uu____4778 =
                   let uu____4784 =
                     let uu____4786 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4786
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4784)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4778)
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
    let uu___17_4811 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___17_4811.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___17_4811.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4832 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4832 with
    | (hd1,args) ->
        let uu____4877 =
          let uu____4892 =
            let uu____4893 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4893.FStar_Syntax_Syntax.n  in
          (uu____4892, args)  in
        (match uu____4877 with
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
         | uu____4965 ->
             (if w
              then
                (let uu____4982 =
                   let uu____4988 =
                     let uu____4990 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4990
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4988)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4982)
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
    let uu____5027 =
      let uu____5028 = FStar_Syntax_Subst.compress t  in
      uu____5028.FStar_Syntax_Syntax.n  in
    match uu____5027 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5034;
          FStar_Syntax_Syntax.rng = uu____5035;_}
        ->
        let uu____5038 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5038
    | uu____5039 ->
        (if w
         then
           (let uu____5042 =
              let uu____5048 =
                let uu____5050 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5050
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5048)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5042)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____5110 uu____5111 =
    let uu____5133 =
      let uu____5139 = FStar_Ident.range_of_id i  in
      let uu____5140 = FStar_Ident.text_of_id i  in (uu____5139, uu____5140)
       in
    embed repr rng uu____5133  in
  let unembed_ident t w uu____5168 =
    let uu____5174 = unembed' w repr t  in
    match uu____5174 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5198 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5198
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5205 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5205
  
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
        let uu____5244 =
          let uu____5249 =
            let uu____5250 =
              let uu____5259 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5259  in
            let uu____5261 =
              let uu____5272 =
                let uu____5281 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5281  in
              let uu____5282 =
                let uu____5293 =
                  let uu____5302 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5302  in
                let uu____5305 =
                  let uu____5316 =
                    let uu____5325 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5325  in
                  let uu____5326 =
                    let uu____5337 =
                      let uu____5346 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5346  in
                    [uu____5337]  in
                  uu____5316 :: uu____5326  in
                uu____5293 :: uu____5305  in
              uu____5272 :: uu____5282  in
            uu____5250 :: uu____5261  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5249
           in
        uu____5244 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5399 =
          let uu____5404 =
            let uu____5405 =
              let uu____5414 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5414  in
            let uu____5418 =
              let uu____5429 =
                let uu____5438 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5438  in
              [uu____5429]  in
            uu____5405 :: uu____5418  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5404
           in
        uu____5399 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5482 =
          let uu____5487 =
            let uu____5488 =
              let uu____5497 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5497  in
            let uu____5501 =
              let uu____5512 =
                let uu____5521 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5521  in
              let uu____5524 =
                let uu____5535 =
                  let uu____5544 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5544  in
                let uu____5545 =
                  let uu____5556 =
                    let uu____5565 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5565  in
                  let uu____5566 =
                    let uu____5577 =
                      let uu____5586 =
                        let uu____5587 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5587 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5586  in
                    [uu____5577]  in
                  uu____5556 :: uu____5566  in
                uu____5535 :: uu____5545  in
              uu____5512 :: uu____5524  in
            uu____5488 :: uu____5501  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5487
           in
        uu____5482 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___18_5653 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___18_5653.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___18_5653.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5672 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5672 with
    | (hd1,args) ->
        let uu____5717 =
          let uu____5730 =
            let uu____5731 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5731.FStar_Syntax_Syntax.n  in
          (uu____5730, args)  in
        (match uu____5717 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5746)::(us,uu____5748)::(bs,uu____5750)::(t2,uu____5752)::
            (dcs,uu____5754)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5819 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5819
               (fun nm1  ->
                  let uu____5837 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5837
                    (fun us1  ->
                       let uu____5851 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5851
                         (fun bs1  ->
                            let uu____5857 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5857
                              (fun t3  ->
                                 let uu____5863 =
                                   let uu____5871 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5871 dcs  in
                                 FStar_Util.bind_opt uu____5863
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_30  ->
                                           FStar_Pervasives_Native.Some _0_30)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5909)::(fvar1,uu____5911)::(univs1,uu____5913)::
            (ty,uu____5915)::(t2,uu____5917)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5982 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5982
               (fun r1  ->
                  let uu____5992 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5992
                    (fun fvar2  ->
                       let uu____5998 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5998
                         (fun univs2  ->
                            let uu____6012 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____6012
                              (fun ty1  ->
                                 let uu____6018 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____6018
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _0_31  ->
                                           FStar_Pervasives_Native.Some _0_31)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6043 ->
             (if w
              then
                (let uu____6058 =
                   let uu____6064 =
                     let uu____6066 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6066
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6064)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6058)
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
          let uu____6092 =
            let uu____6097 =
              let uu____6098 =
                let uu____6107 =
                  let uu____6108 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6108  in
                FStar_Syntax_Syntax.as_arg uu____6107  in
              [uu____6098]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6097
             in
          uu____6092 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6130 =
            let uu____6135 =
              let uu____6136 =
                let uu____6145 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6145  in
              let uu____6146 =
                let uu____6157 =
                  let uu____6166 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6166  in
                [uu____6157]  in
              uu____6136 :: uu____6146  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6135
             in
          uu____6130 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___19_6193 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___19_6193.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___19_6193.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6214 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6214 with
    | (hd1,args) ->
        let uu____6259 =
          let uu____6272 =
            let uu____6273 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6273.FStar_Syntax_Syntax.n  in
          (uu____6272, args)  in
        (match uu____6259 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6303)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6328 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6328
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6337)::(e2,uu____6339)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6374 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6374
               (fun e11  ->
                  let uu____6380 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6380
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_33  -> FStar_Pervasives_Native.Some _0_33)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6387 ->
             (if w
              then
                (let uu____6402 =
                   let uu____6408 =
                     let uu____6410 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6410
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6408)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6402)
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
    let uu____6434 =
      let uu____6439 =
        let uu____6440 =
          let uu____6449 =
            let uu____6450 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____6450  in
          FStar_Syntax_Syntax.as_arg uu____6449  in
        [uu____6440]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____6439
       in
    uu____6434 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6476 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____6476 with
    | (bv,aq) ->
        let uu____6483 =
          let uu____6488 =
            let uu____6489 =
              let uu____6498 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____6498  in
            let uu____6499 =
              let uu____6510 =
                let uu____6519 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____6519  in
              [uu____6510]  in
            uu____6489 :: uu____6499  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____6488
           in
        uu____6483 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6553 =
      let uu____6558 =
        let uu____6559 =
          let uu____6568 =
            let uu____6569 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____6576 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____6569 i.FStar_Syntax_Syntax.rng uu____6576  in
          FStar_Syntax_Syntax.as_arg uu____6568  in
        [uu____6559]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____6558
       in
    uu____6553 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6608 =
      let uu____6613 =
        let uu____6614 =
          let uu____6623 =
            let uu____6624 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____6624  in
          FStar_Syntax_Syntax.as_arg uu____6623  in
        [uu____6614]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____6613
       in
    uu____6608 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6656 =
      let uu____6661 =
        let uu____6662 =
          let uu____6671 =
            let uu____6672 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____6672  in
          FStar_Syntax_Syntax.as_arg uu____6671  in
        [uu____6662]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6661
       in
    uu____6656 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  