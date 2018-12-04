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
    let uu___239_570 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___239_570.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___239_570.FStar_Syntax_Syntax.vars)
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
       in
    let uu___240_1089 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___240_1089.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___240_1089.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1110 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1110 with
    | (hd1,args) ->
        let uu____1155 =
          let uu____1170 =
            let uu____1171 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1171.FStar_Syntax_Syntax.n  in
          (uu____1170, args)  in
        (match uu____1155 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1245)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1280 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1280
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1289)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1324 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1324
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____1337)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1372 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____1372
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _0_3  -> FStar_Pervasives_Native.Some _0_3)
                    (FStar_Reflection_Data.C_Range r1))
         | uu____1379 ->
             (if w
              then
                (let uu____1396 =
                   let uu____1402 =
                     let uu____1404 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1404
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1402)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1396)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1417  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1430 =
            let uu____1435 =
              let uu____1436 =
                let uu____1445 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1445  in
              [uu____1436]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1435
             in
          uu____1430 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1470 =
            let uu____1475 =
              let uu____1476 =
                let uu____1485 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1485  in
              let uu____1486 =
                let uu____1497 =
                  let uu____1506 =
                    let uu____1507 =
                      let uu____1512 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1512  in
                    embed uu____1507 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1506  in
                [uu____1497]  in
              uu____1476 :: uu____1486  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1475
             in
          uu____1470 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1544 =
            let uu____1549 =
              let uu____1550 =
                let uu____1559 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1559  in
              [uu____1550]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1549
             in
          uu____1544 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1579 =
            let uu____1584 =
              let uu____1585 =
                let uu____1594 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1594  in
              [uu____1585]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1584
             in
          uu____1579 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1615 =
            let uu____1620 =
              let uu____1621 =
                let uu____1630 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1630  in
              let uu____1631 =
                let uu____1642 =
                  let uu____1651 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1651  in
                [uu____1642]  in
              uu____1621 :: uu____1631  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1620
             in
          uu____1615 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1696 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1696 with
      | (hd1,args) ->
          let uu____1741 =
            let uu____1754 =
              let uu____1755 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1755.FStar_Syntax_Syntax.n  in
            (uu____1754, args)  in
          (match uu____1741 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1770)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1795 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1795
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_Pervasives_Native.Some _0_4)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1804)::(ps,uu____1806)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1841 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1841
                 (fun f1  ->
                    let uu____1847 =
                      let uu____1852 =
                        let uu____1857 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1857  in
                      unembed' w uu____1852 ps  in
                    FStar_Util.bind_opt uu____1847
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_5  -> FStar_Pervasives_Native.Some _0_5)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1874)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1899 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1899
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_6  -> FStar_Pervasives_Native.Some _0_6)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1908)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1933 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1933
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_7  -> FStar_Pervasives_Native.Some _0_7)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1942)::(t2,uu____1944)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1979 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____1979
                 (fun bv1  ->
                    let uu____1985 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1985
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_8  -> FStar_Pervasives_Native.Some _0_8)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1992 ->
               (if w
                then
                  (let uu____2007 =
                     let uu____2013 =
                       let uu____2015 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2015
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2013)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2007)
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
    let uu____2042 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2042
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2057 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2057 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2080 =
            let uu____2085 =
              let uu____2086 =
                let uu____2095 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2095  in
              [uu____2086]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____2085
             in
          uu____2080 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2115 =
            let uu____2120 =
              let uu____2121 =
                let uu____2130 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2130  in
              [uu____2121]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2120
             in
          uu____2115 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2150 =
            let uu____2155 =
              let uu____2156 =
                let uu____2165 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2165  in
              [uu____2156]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2155
             in
          uu____2150 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2186 =
            let uu____2191 =
              let uu____2192 =
                let uu____2201 =
                  let uu____2202 = e_term_aq aq  in embed uu____2202 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2201  in
              let uu____2205 =
                let uu____2216 =
                  let uu____2225 =
                    let uu____2226 = e_argv_aq aq  in embed uu____2226 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2225  in
                [uu____2216]  in
              uu____2192 :: uu____2205  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2191
             in
          uu____2186 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2265 =
            let uu____2270 =
              let uu____2271 =
                let uu____2280 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2280  in
              let uu____2281 =
                let uu____2292 =
                  let uu____2301 =
                    let uu____2302 = e_term_aq aq  in embed uu____2302 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2301  in
                [uu____2292]  in
              uu____2271 :: uu____2281  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2270
             in
          uu____2265 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2333 =
            let uu____2338 =
              let uu____2339 =
                let uu____2348 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2348  in
              let uu____2349 =
                let uu____2360 =
                  let uu____2369 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2369  in
                [uu____2360]  in
              uu____2339 :: uu____2349  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2338
             in
          uu____2333 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2397 =
            let uu____2402 =
              let uu____2403 =
                let uu____2412 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2412  in
              [uu____2403]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2402
             in
          uu____2397 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2433 =
            let uu____2438 =
              let uu____2439 =
                let uu____2448 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2448  in
              let uu____2449 =
                let uu____2460 =
                  let uu____2469 =
                    let uu____2470 = e_term_aq aq  in embed uu____2470 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2469  in
                [uu____2460]  in
              uu____2439 :: uu____2449  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2438
             in
          uu____2433 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2500 =
            let uu____2505 =
              let uu____2506 =
                let uu____2515 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2515  in
              [uu____2506]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2505
             in
          uu____2500 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2536 =
            let uu____2541 =
              let uu____2542 =
                let uu____2551 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2551  in
              let uu____2552 =
                let uu____2563 =
                  let uu____2572 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2572  in
                [uu____2563]  in
              uu____2542 :: uu____2552  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2541
             in
          uu____2536 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2609 =
            let uu____2614 =
              let uu____2615 =
                let uu____2624 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2624  in
              let uu____2626 =
                let uu____2637 =
                  let uu____2646 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____2646  in
                let uu____2647 =
                  let uu____2658 =
                    let uu____2667 =
                      let uu____2668 = e_term_aq aq  in
                      embed uu____2668 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2667  in
                  let uu____2671 =
                    let uu____2682 =
                      let uu____2691 =
                        let uu____2692 = e_term_aq aq  in
                        embed uu____2692 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2691  in
                    [uu____2682]  in
                  uu____2658 :: uu____2671  in
                uu____2637 :: uu____2647  in
              uu____2615 :: uu____2626  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2614
             in
          uu____2609 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2743 =
            let uu____2748 =
              let uu____2749 =
                let uu____2758 =
                  let uu____2759 = e_term_aq aq  in embed uu____2759 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____2758  in
              let uu____2762 =
                let uu____2773 =
                  let uu____2782 =
                    let uu____2783 =
                      let uu____2792 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2792  in
                    embed uu____2783 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2782  in
                [uu____2773]  in
              uu____2749 :: uu____2762  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2748
             in
          uu____2743 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2842 =
            let uu____2847 =
              let uu____2848 =
                let uu____2857 =
                  let uu____2858 = e_term_aq aq  in embed uu____2858 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2857  in
              let uu____2861 =
                let uu____2872 =
                  let uu____2881 =
                    let uu____2882 = e_term_aq aq  in embed uu____2882 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2881  in
                let uu____2885 =
                  let uu____2896 =
                    let uu____2905 =
                      let uu____2906 =
                        let uu____2911 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2911  in
                      embed uu____2906 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2905  in
                  [uu____2896]  in
                uu____2872 :: uu____2885  in
              uu____2848 :: uu____2861  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2847
             in
          uu____2842 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2957 =
            let uu____2962 =
              let uu____2963 =
                let uu____2972 =
                  let uu____2973 = e_term_aq aq  in embed uu____2973 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____2972  in
              let uu____2976 =
                let uu____2987 =
                  let uu____2996 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2996  in
                let uu____2997 =
                  let uu____3008 =
                    let uu____3017 =
                      let uu____3018 =
                        let uu____3023 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3023  in
                      embed uu____3018 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3017  in
                  [uu____3008]  in
                uu____2987 :: uu____2997  in
              uu____2963 :: uu____2976  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2962
             in
          uu____2957 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___241_3062 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___241_3062.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___241_3062.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3080 = FStar_Syntax_Util.head_and_args t  in
      match uu____3080 with
      | (hd1,args) ->
          let uu____3125 =
            let uu____3138 =
              let uu____3139 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3139.FStar_Syntax_Syntax.n  in
            (uu____3138, args)  in
          (match uu____3125 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3154)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3179 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3179
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_9  -> FStar_Pervasives_Native.Some _0_9)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3188)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3213 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3213
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_10  -> FStar_Pervasives_Native.Some _0_10)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3222)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3247 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3247
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_11  -> FStar_Pervasives_Native.Some _0_11)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3256)::(r,uu____3258)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3293 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3293
                 (fun l1  ->
                    let uu____3299 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3299
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_12  -> FStar_Pervasives_Native.Some _0_12)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3308)::(t1,uu____3310)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3345 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3345
                 (fun b1  ->
                    let uu____3351 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3351
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_13  -> FStar_Pervasives_Native.Some _0_13)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3360)::(t1,uu____3362)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3397 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3397
                 (fun b1  ->
                    let uu____3403 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3403
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3412)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3437 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3437
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_15  -> FStar_Pervasives_Native.Some _0_15)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3446)::(t1,uu____3448)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3483 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3483
                 (fun b1  ->
                    let uu____3489 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3489
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3498)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3523 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3523
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3532)::(l,uu____3534)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3569 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3569
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3580)::(b,uu____3582)::(t1,uu____3584)::(t2,uu____3586)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3641 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3641
                 (fun r1  ->
                    let uu____3651 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3651
                      (fun b1  ->
                         let uu____3657 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3657
                           (fun t11  ->
                              let uu____3663 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____3663
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_19  ->
                                        FStar_Pervasives_Native.Some _0_19)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3673)::(brs,uu____3675)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3710 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3710
                 (fun t2  ->
                    let uu____3716 =
                      let uu____3721 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____3721 brs  in
                    FStar_Util.bind_opt uu____3716
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3740)::(t1,uu____3742)::(tacopt,uu____3744)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3789 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3789
                 (fun e1  ->
                    let uu____3795 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3795
                      (fun t2  ->
                         let uu____3801 =
                           let uu____3806 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3806 tacopt  in
                         FStar_Util.bind_opt uu____3801
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_21  ->
                                   FStar_Pervasives_Native.Some _0_21)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3825)::(c,uu____3827)::(tacopt,uu____3829)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3874 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____3874
                 (fun e1  ->
                    let uu____3880 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3880
                      (fun c1  ->
                         let uu____3886 =
                           let uu____3891 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____3891 tacopt  in
                         FStar_Util.bind_opt uu____3886
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_22  ->
                                   FStar_Pervasives_Native.Some _0_22)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____3925 ->
               (if w
                then
                  (let uu____3940 =
                     let uu____3946 =
                       let uu____3948 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3948
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3946)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3940)
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
    let uu____3977 =
      let uu____3982 =
        let uu____3983 =
          let uu____3992 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3992  in
        let uu____3994 =
          let uu____4005 =
            let uu____4014 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4014  in
          let uu____4015 =
            let uu____4026 =
              let uu____4035 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4035  in
            [uu____4026]  in
          uu____4005 :: uu____4015  in
        uu____3983 :: uu____3994  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3982
       in
    uu____3977 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4088 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4088 with
    | (hd1,args) ->
        let uu____4133 =
          let uu____4146 =
            let uu____4147 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4147.FStar_Syntax_Syntax.n  in
          (uu____4146, args)  in
        (match uu____4133 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4162)::(idx,uu____4164)::(s,uu____4166)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4211 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4211
               (fun nm1  ->
                  let uu____4221 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4221
                    (fun idx1  ->
                       let uu____4227 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4227
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_24  ->
                                 FStar_Pervasives_Native.Some _0_24)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4234 ->
             (if w
              then
                (let uu____4249 =
                   let uu____4255 =
                     let uu____4257 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4257
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4255)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4249)
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
        let uu____4283 =
          let uu____4288 =
            let uu____4289 =
              let uu____4298 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4298  in
            let uu____4299 =
              let uu____4310 =
                let uu____4319 =
                  let uu____4320 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4320 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4319  in
              [uu____4310]  in
            uu____4289 :: uu____4299  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4288
           in
        uu____4283 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4358 =
          let uu____4363 =
            let uu____4364 =
              let uu____4373 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4373  in
            let uu____4374 =
              let uu____4385 =
                let uu____4394 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4394  in
              [uu____4385]  in
            uu____4364 :: uu____4374  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4363
           in
        uu____4358 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___242_4421 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___242_4421.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___242_4421.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4440 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4440 with
    | (hd1,args) ->
        let uu____4485 =
          let uu____4498 =
            let uu____4499 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4499.FStar_Syntax_Syntax.n  in
          (uu____4498, args)  in
        (match uu____4485 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4514)::(md,uu____4516)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4551 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____4551
               (fun t3  ->
                  let uu____4557 =
                    let uu____4562 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____4562 md  in
                  FStar_Util.bind_opt uu____4557
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4581)::(post,uu____4583)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4618 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____4618
               (fun pre1  ->
                  let uu____4624 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4624
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
               FStar_Reflection_Data.C_Unknown
         | uu____4648 ->
             (if w
              then
                (let uu____4663 =
                   let uu____4669 =
                     let uu____4671 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4671
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4669)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4663)
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
    let uu___243_4696 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___243_4696.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___243_4696.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4717 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4717 with
    | (hd1,args) ->
        let uu____4762 =
          let uu____4777 =
            let uu____4778 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4778.FStar_Syntax_Syntax.n  in
          (uu____4777, args)  in
        (match uu____4762 with
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
         | uu____4850 ->
             (if w
              then
                (let uu____4867 =
                   let uu____4873 =
                     let uu____4875 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4875
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4873)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4867)
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
    let uu____4912 =
      let uu____4913 = FStar_Syntax_Subst.compress t  in
      uu____4913.FStar_Syntax_Syntax.n  in
    match uu____4912 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____4919;
          FStar_Syntax_Syntax.rng = uu____4920;_}
        ->
        let uu____4923 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____4923
    | uu____4924 ->
        (if w
         then
           (let uu____4927 =
              let uu____4933 =
                let uu____4935 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4935
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4933)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4927)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____4995 uu____4996 =
    let uu____5018 =
      let uu____5024 = FStar_Ident.range_of_id i  in
      let uu____5025 = FStar_Ident.text_of_id i  in (uu____5024, uu____5025)
       in
    embed repr rng uu____5018  in
  let unembed_ident t w uu____5053 =
    let uu____5059 = unembed' w repr t  in
    match uu____5059 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5083 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5083
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5090 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5090
  
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
        let uu____5129 =
          let uu____5134 =
            let uu____5135 =
              let uu____5144 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5144  in
            let uu____5146 =
              let uu____5157 =
                let uu____5166 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5166  in
              let uu____5167 =
                let uu____5178 =
                  let uu____5187 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5187  in
                let uu____5190 =
                  let uu____5201 =
                    let uu____5210 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5210  in
                  let uu____5211 =
                    let uu____5222 =
                      let uu____5231 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5231  in
                    [uu____5222]  in
                  uu____5201 :: uu____5211  in
                uu____5178 :: uu____5190  in
              uu____5157 :: uu____5167  in
            uu____5135 :: uu____5146  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5134
           in
        uu____5129 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____5284 =
          let uu____5289 =
            let uu____5290 =
              let uu____5299 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5299  in
            let uu____5303 =
              let uu____5314 =
                let uu____5323 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____5323  in
              [uu____5314]  in
            uu____5290 :: uu____5303  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____5289
           in
        uu____5284 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____5367 =
          let uu____5372 =
            let uu____5373 =
              let uu____5382 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____5382  in
            let uu____5386 =
              let uu____5397 =
                let uu____5406 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____5406  in
              let uu____5409 =
                let uu____5420 =
                  let uu____5429 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____5429  in
                let uu____5430 =
                  let uu____5441 =
                    let uu____5450 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____5450  in
                  let uu____5451 =
                    let uu____5462 =
                      let uu____5471 =
                        let uu____5472 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____5472 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5471  in
                    [uu____5462]  in
                  uu____5441 :: uu____5451  in
                uu____5420 :: uu____5430  in
              uu____5397 :: uu____5409  in
            uu____5373 :: uu____5386  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____5372
           in
        uu____5367 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___244_5538 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___244_5538.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___244_5538.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5557 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5557 with
    | (hd1,args) ->
        let uu____5602 =
          let uu____5615 =
            let uu____5616 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5616.FStar_Syntax_Syntax.n  in
          (uu____5615, args)  in
        (match uu____5602 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5631)::(us,uu____5633)::(bs,uu____5635)::(t2,uu____5637)::
            (dcs,uu____5639)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5704 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____5704
               (fun nm1  ->
                  let uu____5722 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5722
                    (fun us1  ->
                       let uu____5736 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5736
                         (fun bs1  ->
                            let uu____5742 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____5742
                              (fun t3  ->
                                 let uu____5748 =
                                   let uu____5756 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____5756 dcs  in
                                 FStar_Util.bind_opt uu____5748
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_28  ->
                                           FStar_Pervasives_Native.Some _0_28)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5794)::(fvar1,uu____5796)::(univs1,uu____5798)::
            (ty,uu____5800)::(t2,uu____5802)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5867 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____5867
               (fun r1  ->
                  let uu____5877 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5877
                    (fun fvar2  ->
                       let uu____5883 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____5883
                         (fun univs2  ->
                            let uu____5897 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____5897
                              (fun ty1  ->
                                 let uu____5903 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____5903
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _0_29  ->
                                           FStar_Pervasives_Native.Some _0_29)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____5928 ->
             (if w
              then
                (let uu____5943 =
                   let uu____5949 =
                     let uu____5951 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5951
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5949)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5943)
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
          let uu____5977 =
            let uu____5982 =
              let uu____5983 =
                let uu____5992 =
                  let uu____5993 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5993  in
                FStar_Syntax_Syntax.as_arg uu____5992  in
              [uu____5983]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5982
             in
          uu____5977 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6015 =
            let uu____6020 =
              let uu____6021 =
                let uu____6030 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6030  in
              let uu____6031 =
                let uu____6042 =
                  let uu____6051 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6051  in
                [uu____6042]  in
              uu____6021 :: uu____6031  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6020
             in
          uu____6015 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___245_6078 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___245_6078.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___245_6078.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6099 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6099 with
    | (hd1,args) ->
        let uu____6144 =
          let uu____6157 =
            let uu____6158 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6158.FStar_Syntax_Syntax.n  in
          (uu____6157, args)  in
        (match uu____6144 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6188)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6213 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6213
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6222)::(e2,uu____6224)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____6259 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____6259
               (fun e11  ->
                  let uu____6265 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____6265
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____6272 ->
             (if w
              then
                (let uu____6287 =
                   let uu____6293 =
                     let uu____6295 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____6295
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6293)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6287)
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
    let uu____6319 =
      let uu____6324 =
        let uu____6325 =
          let uu____6334 =
            let uu____6335 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____6335  in
          FStar_Syntax_Syntax.as_arg uu____6334  in
        [uu____6325]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____6324
       in
    uu____6319 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6361 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____6361 with
    | (bv,aq) ->
        let uu____6368 =
          let uu____6373 =
            let uu____6374 =
              let uu____6383 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____6383  in
            let uu____6384 =
              let uu____6395 =
                let uu____6404 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____6404  in
              [uu____6395]  in
            uu____6374 :: uu____6384  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____6373
           in
        uu____6368 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6438 =
      let uu____6443 =
        let uu____6444 =
          let uu____6453 =
            let uu____6454 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____6461 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____6454 i.FStar_Syntax_Syntax.rng uu____6461  in
          FStar_Syntax_Syntax.as_arg uu____6453  in
        [uu____6444]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____6443
       in
    uu____6438 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6493 =
      let uu____6498 =
        let uu____6499 =
          let uu____6508 =
            let uu____6509 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____6509  in
          FStar_Syntax_Syntax.as_arg uu____6508  in
        [uu____6499]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____6498
       in
    uu____6493 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6541 =
      let uu____6546 =
        let uu____6547 =
          let uu____6556 =
            let uu____6557 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____6557  in
          FStar_Syntax_Syntax.as_arg uu____6556  in
        [uu____6547]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6546
       in
    uu____6541 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  