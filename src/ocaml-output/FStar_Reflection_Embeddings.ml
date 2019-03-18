open Prims
let mk_emb :
  'Auu____59353 .
    (FStar_Range.range -> 'Auu____59353 -> FStar_Syntax_Syntax.term) ->
      (Prims.bool ->
         FStar_Syntax_Syntax.term ->
           'Auu____59353 FStar_Pervasives_Native.option)
        ->
        FStar_Syntax_Syntax.term ->
          'Auu____59353 FStar_Syntax_Embeddings.embedding
  =
  fun f  ->
    fun g  ->
      fun t  ->
        let uu____59397 = FStar_Syntax_Embeddings.term_as_fv t  in
        FStar_Syntax_Embeddings.mk_emb
          (fun x  -> fun r  -> fun _topt  -> fun _norm  -> f r x)
          (fun x  -> fun w  -> fun _norm  -> g w x) uu____59397
  
let embed :
  'Auu____59424 .
    'Auu____59424 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range -> 'Auu____59424 -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun r  ->
      fun x  ->
        let uu____59444 = FStar_Syntax_Embeddings.embed e x  in
        uu____59444 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings.id_norm_cb
  
let unembed' :
  'Auu____59462 .
    Prims.bool ->
      'Auu____59462 FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          'Auu____59462 FStar_Pervasives_Native.option
  =
  fun w  ->
    fun e  ->
      fun x  ->
        let uu____59486 = FStar_Syntax_Embeddings.unembed e x  in
        uu____59486 w FStar_Syntax_Embeddings.id_norm_cb
  
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____59524 =
      let uu____59525 = FStar_Syntax_Subst.compress t  in
      uu____59525.FStar_Syntax_Syntax.n  in
    match uu____59524 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ;
          FStar_Syntax_Syntax.ltyp = uu____59531;
          FStar_Syntax_Syntax.rng = uu____59532;_}
        ->
        let uu____59535 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59535
    | uu____59536 ->
        (if w
         then
           (let uu____59539 =
              let uu____59545 =
                let uu____59547 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____59547  in
              (FStar_Errors.Warning_NotEmbedded, uu____59545)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59539)
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
    let uu____59584 =
      let uu____59585 = FStar_Syntax_Subst.compress t  in
      uu____59585.FStar_Syntax_Syntax.n  in
    match uu____59584 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ;
          FStar_Syntax_Syntax.ltyp = uu____59591;
          FStar_Syntax_Syntax.rng = uu____59592;_}
        ->
        let uu____59595 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____59595
    | uu____59596 ->
        (if w
         then
           (let uu____59599 =
              let uu____59605 =
                let uu____59607 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____59607
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____59605)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____59599)
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
          let uu____59659 = f x  in
          FStar_Util.bind_opt uu____59659
            (fun x1  ->
               let uu____59667 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____59667
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
        let uu____59736 =
          mapM_opt
            (fun uu____59749  ->
               match uu____59749 with
               | (bv,e) ->
                   let uu____59758 = unembed_term w e  in
                   FStar_Util.bind_opt uu____59758
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____59736
          (fun s  ->
             let uu____59772 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____59772)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____59774 =
        let uu____59775 = FStar_Syntax_Subst.compress t1  in
        uu____59775.FStar_Syntax_Syntax.n  in
      match uu____59774 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____59786 ->
          (if w
           then
             (let uu____59789 =
                let uu____59795 =
                  let uu____59797 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____59797
                   in
                (FStar_Errors.Warning_NotEmbedded, uu____59795)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____59789)
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
          let uu____59832 =
            let uu____59837 =
              let uu____59838 =
                let uu____59847 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____59847  in
              [uu____59838]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____59837
             in
          uu____59832 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___625_59864 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___625_59864.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___625_59864.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____59885 = FStar_Syntax_Util.head_and_args t1  in
    match uu____59885 with
    | (hd1,args) ->
        let uu____59930 =
          let uu____59945 =
            let uu____59946 = FStar_Syntax_Util.un_uinst hd1  in
            uu____59946.FStar_Syntax_Syntax.n  in
          (uu____59945, args)  in
        (match uu____59930 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____60001)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____60036 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____60036
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____60041 ->
             (if w
              then
                (let uu____60058 =
                   let uu____60064 =
                     let uu____60066 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____60066
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60064)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60058)
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
    let uu____60106 =
      let uu____60107 = FStar_Syntax_Subst.compress t  in
      uu____60107.FStar_Syntax_Syntax.n  in
    match uu____60106 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____60113;
          FStar_Syntax_Syntax.rng = uu____60114;_}
        ->
        let uu____60117 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60117
    | uu____60118 ->
        (if w
         then
           (let uu____60121 =
              let uu____60127 =
                let uu____60129 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____60129  in
              (FStar_Errors.Warning_NotEmbedded, uu____60127)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60121)
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
    let uu____60166 =
      let uu____60167 = FStar_Syntax_Subst.compress t  in
      uu____60167.FStar_Syntax_Syntax.n  in
    match uu____60166 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____60173;
          FStar_Syntax_Syntax.rng = uu____60174;_}
        ->
        let uu____60177 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60177
    | uu____60178 ->
        (if w
         then
           (let uu____60181 =
              let uu____60187 =
                let uu____60189 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____60189  in
              (FStar_Errors.Warning_NotEmbedded, uu____60187)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60181)
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
    let uu____60226 =
      let uu____60227 = FStar_Syntax_Subst.compress t  in
      uu____60227.FStar_Syntax_Syntax.n  in
    match uu____60226 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____60233;
          FStar_Syntax_Syntax.rng = uu____60234;_}
        ->
        let uu____60237 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____60237
    | uu____60238 ->
        (if w
         then
           (let uu____60241 =
              let uu____60247 =
                let uu____60249 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____60249  in
              (FStar_Errors.Warning_NotEmbedded, uu____60247)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____60241)
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
          let uu____60275 =
            let uu____60280 =
              let uu____60281 =
                let uu____60290 =
                  let uu____60291 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____60291  in
                FStar_Syntax_Syntax.as_arg uu____60290  in
              [uu____60281]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____60280
             in
          uu____60275 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____60311 =
            let uu____60316 =
              let uu____60317 =
                let uu____60326 =
                  embed FStar_Syntax_Embeddings.e_string rng s  in
                FStar_Syntax_Syntax.as_arg uu____60326  in
              [uu____60317]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____60316
             in
          uu____60311 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____60345 =
            let uu____60350 =
              let uu____60351 =
                let uu____60360 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____60360  in
              [uu____60351]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____60350
             in
          uu____60345 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____60378 =
            let uu____60383 =
              let uu____60384 =
                let uu____60393 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____60393  in
              [uu____60384]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____60383
             in
          uu____60378 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___714_60413 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_60413.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_60413.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____60434 = FStar_Syntax_Util.head_and_args t1  in
    match uu____60434 with
    | (hd1,args) ->
        let uu____60479 =
          let uu____60494 =
            let uu____60495 = FStar_Syntax_Util.un_uinst hd1  in
            uu____60495.FStar_Syntax_Syntax.n  in
          (uu____60494, args)  in
        (match uu____60479 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____60569)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____60604 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____60604
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _60611  -> FStar_Pervasives_Native.Some _60611)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____60614)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____60649 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____60649
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _60660  -> FStar_Pervasives_Native.Some _60660)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____60663)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____60698 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____60698
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _60705  -> FStar_Pervasives_Native.Some _60705)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _60727  -> FStar_Pervasives_Native.Some _60727)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____60730)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____60765 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____60765
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _60784  -> FStar_Pervasives_Native.Some _60784)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____60785 ->
             (if w
              then
                (let uu____60802 =
                   let uu____60808 =
                     let uu____60810 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____60810
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____60808)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____60802)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____60823  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____60836 =
            let uu____60841 =
              let uu____60842 =
                let uu____60851 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____60851  in
              [uu____60842]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____60841
             in
          uu____60836 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____60874 =
            let uu____60879 =
              let uu____60880 =
                let uu____60889 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____60889  in
              let uu____60890 =
                let uu____60901 =
                  let uu____60910 =
                    let uu____60911 =
                      let uu____60916 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____60916  in
                    embed uu____60911 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____60910  in
                [uu____60901]  in
              uu____60880 :: uu____60890  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____60879
             in
          uu____60874 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____60946 =
            let uu____60951 =
              let uu____60952 =
                let uu____60961 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____60961  in
              [uu____60952]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____60951
             in
          uu____60946 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____60979 =
            let uu____60984 =
              let uu____60985 =
                let uu____60994 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____60994  in
              [uu____60985]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____60984
             in
          uu____60979 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____61013 =
            let uu____61018 =
              let uu____61019 =
                let uu____61028 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61028  in
              let uu____61029 =
                let uu____61040 =
                  let uu____61049 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____61049  in
                [uu____61040]  in
              uu____61019 :: uu____61029  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____61018
             in
          uu____61013 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____61092 = FStar_Syntax_Util.head_and_args t1  in
      match uu____61092 with
      | (hd1,args) ->
          let uu____61137 =
            let uu____61150 =
              let uu____61151 = FStar_Syntax_Util.un_uinst hd1  in
              uu____61151.FStar_Syntax_Syntax.n  in
            (uu____61150, args)  in
          (match uu____61137 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____61166)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____61191 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____61191
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _61198  -> FStar_Pervasives_Native.Some _61198)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____61201)::(ps,uu____61203)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____61238 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____61238
                 (fun f1  ->
                    let uu____61244 =
                      let uu____61249 =
                        let uu____61254 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____61254  in
                      unembed' w uu____61249 ps  in
                    FStar_Util.bind_opt uu____61244
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _61267  ->
                              FStar_Pervasives_Native.Some _61267)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61272)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____61297 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61297
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61304  -> FStar_Pervasives_Native.Some _61304)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____61307)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____61332 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61332
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _61339  -> FStar_Pervasives_Native.Some _61339)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____61342)::(t2,uu____61344)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____61379 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____61379
                 (fun bv1  ->
                    let uu____61385 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____61385
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _61392  ->
                              FStar_Pervasives_Native.Some _61392)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____61393 ->
               (if w
                then
                  (let uu____61408 =
                     let uu____61414 =
                       let uu____61416 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____61416
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____61414)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____61408)
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
    let uu____61443 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____61443
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____61458 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____61458 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____61481 =
            let uu____61486 =
              let uu____61487 =
                let uu____61496 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61496  in
              [uu____61487]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____61486
             in
          uu____61481 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____61514 =
            let uu____61519 =
              let uu____61520 =
                let uu____61529 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____61529  in
              [uu____61520]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____61519
             in
          uu____61514 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____61547 =
            let uu____61552 =
              let uu____61553 =
                let uu____61562 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61562  in
              [uu____61553]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____61552
             in
          uu____61547 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____61581 =
            let uu____61586 =
              let uu____61587 =
                let uu____61596 =
                  let uu____61597 = e_term_aq aq  in
                  embed uu____61597 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____61596  in
              let uu____61600 =
                let uu____61611 =
                  let uu____61620 =
                    let uu____61621 = e_argv_aq aq  in
                    embed uu____61621 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____61620  in
                [uu____61611]  in
              uu____61587 :: uu____61600  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____61586
             in
          uu____61581 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____61658 =
            let uu____61663 =
              let uu____61664 =
                let uu____61673 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61673  in
              let uu____61674 =
                let uu____61685 =
                  let uu____61694 =
                    let uu____61695 = e_term_aq aq  in
                    embed uu____61695 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61694  in
                [uu____61685]  in
              uu____61664 :: uu____61674  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____61663
             in
          uu____61658 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____61724 =
            let uu____61729 =
              let uu____61730 =
                let uu____61739 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____61739  in
              let uu____61740 =
                let uu____61751 =
                  let uu____61760 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____61760  in
                [uu____61751]  in
              uu____61730 :: uu____61740  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____61729
             in
          uu____61724 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____61786 =
            let uu____61791 =
              let uu____61792 =
                let uu____61801 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____61801  in
              [uu____61792]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____61791
             in
          uu____61786 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____61820 =
            let uu____61825 =
              let uu____61826 =
                let uu____61835 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____61835  in
              let uu____61836 =
                let uu____61847 =
                  let uu____61856 =
                    let uu____61857 = e_term_aq aq  in
                    embed uu____61857 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____61856  in
                [uu____61847]  in
              uu____61826 :: uu____61836  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____61825
             in
          uu____61820 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____61885 =
            let uu____61890 =
              let uu____61891 =
                let uu____61900 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____61900  in
              [uu____61891]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____61890
             in
          uu____61885 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____61919 =
            let uu____61924 =
              let uu____61925 =
                let uu____61934 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____61934  in
              let uu____61935 =
                let uu____61946 =
                  let uu____61955 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____61955  in
                [uu____61946]  in
              uu____61925 :: uu____61935  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____61924
             in
          uu____61919 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____61990 =
            let uu____61995 =
              let uu____61996 =
                let uu____62005 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____62005  in
              let uu____62007 =
                let uu____62018 =
                  let uu____62027 = embed e_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____62027  in
                let uu____62028 =
                  let uu____62039 =
                    let uu____62048 =
                      let uu____62049 = e_term_aq aq  in
                      embed uu____62049 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____62048  in
                  let uu____62052 =
                    let uu____62063 =
                      let uu____62072 =
                        let uu____62073 = e_term_aq aq  in
                        embed uu____62073 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____62072  in
                    [uu____62063]  in
                  uu____62039 :: uu____62052  in
                uu____62018 :: uu____62028  in
              uu____61996 :: uu____62007  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____61995
             in
          uu____61990 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____62122 =
            let uu____62127 =
              let uu____62128 =
                let uu____62137 =
                  let uu____62138 = e_term_aq aq  in embed uu____62138 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____62137  in
              let uu____62141 =
                let uu____62152 =
                  let uu____62161 =
                    let uu____62162 =
                      let uu____62171 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____62171  in
                    embed uu____62162 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____62161  in
                [uu____62152]  in
              uu____62128 :: uu____62141  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____62127
             in
          uu____62122 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____62219 =
            let uu____62224 =
              let uu____62225 =
                let uu____62234 =
                  let uu____62235 = e_term_aq aq  in embed uu____62235 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62234  in
              let uu____62238 =
                let uu____62249 =
                  let uu____62258 =
                    let uu____62259 = e_term_aq aq  in
                    embed uu____62259 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____62258  in
                let uu____62262 =
                  let uu____62273 =
                    let uu____62282 =
                      let uu____62283 =
                        let uu____62288 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62288  in
                      embed uu____62283 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62282  in
                  [uu____62273]  in
                uu____62249 :: uu____62262  in
              uu____62225 :: uu____62238  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____62224
             in
          uu____62219 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____62332 =
            let uu____62337 =
              let uu____62338 =
                let uu____62347 =
                  let uu____62348 = e_term_aq aq  in embed uu____62348 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____62347  in
              let uu____62351 =
                let uu____62362 =
                  let uu____62371 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____62371  in
                let uu____62372 =
                  let uu____62383 =
                    let uu____62392 =
                      let uu____62393 =
                        let uu____62398 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____62398  in
                      embed uu____62393 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____62392  in
                  [uu____62383]  in
                uu____62362 :: uu____62372  in
              uu____62338 :: uu____62351  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____62337
             in
          uu____62332 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___907_62435 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___907_62435.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___907_62435.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____62453 = FStar_Syntax_Util.head_and_args t  in
      match uu____62453 with
      | (hd1,args) ->
          let uu____62498 =
            let uu____62511 =
              let uu____62512 = FStar_Syntax_Util.un_uinst hd1  in
              uu____62512.FStar_Syntax_Syntax.n  in
            (uu____62511, args)  in
          (match uu____62498 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62527)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____62552 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62552
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62559  -> FStar_Pervasives_Native.Some _62559)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____62562)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____62587 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62587
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _62594  -> FStar_Pervasives_Native.Some _62594)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____62597)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____62622 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____62622
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _62629  -> FStar_Pervasives_Native.Some _62629)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____62632)::(r,uu____62634)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____62669 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____62669
                 (fun l1  ->
                    let uu____62675 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____62675
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _62682  ->
                              FStar_Pervasives_Native.Some _62682)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62685)::(t1,uu____62687)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____62722 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62722
                 (fun b1  ->
                    let uu____62728 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62728
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62735  ->
                              FStar_Pervasives_Native.Some _62735)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62738)::(t1,uu____62740)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____62775 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____62775
                 (fun b1  ->
                    let uu____62781 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____62781
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _62788  ->
                              FStar_Pervasives_Native.Some _62788)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____62791)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____62816 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____62816
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _62823  -> FStar_Pervasives_Native.Some _62823)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____62826)::(t1,uu____62828)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____62863 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____62863
                 (fun b1  ->
                    let uu____62869 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____62869
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _62876  ->
                              FStar_Pervasives_Native.Some _62876)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____62879)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____62904 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____62904
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _62911  -> FStar_Pervasives_Native.Some _62911)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____62914)::(l,uu____62916)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____62951 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____62951
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _62960  -> FStar_Pervasives_Native.Some _62960)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____62963)::(b,uu____62965)::(t1,uu____62967)::
              (t2,uu____62969)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____63024 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____63024
                 (fun r1  ->
                    let uu____63034 = unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____63034
                      (fun b1  ->
                         let uu____63040 = unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____63040
                           (fun t11  ->
                              let uu____63046 = unembed' w e_term t2  in
                              FStar_Util.bind_opt uu____63046
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _63053  ->
                                        FStar_Pervasives_Native.Some _63053)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____63057)::(brs,uu____63059)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____63094 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____63094
                 (fun t2  ->
                    let uu____63100 =
                      let uu____63105 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____63105 brs  in
                    FStar_Util.bind_opt uu____63100
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _63120  ->
                              FStar_Pervasives_Native.Some _63120)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63125)::(t1,uu____63127)::(tacopt,uu____63129)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____63174 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63174
                 (fun e1  ->
                    let uu____63180 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____63180
                      (fun t2  ->
                         let uu____63186 =
                           let uu____63191 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63191 tacopt  in
                         FStar_Util.bind_opt uu____63186
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63206  ->
                                   FStar_Pervasives_Native.Some _63206)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____63211)::(c,uu____63213)::(tacopt,uu____63215)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____63260 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____63260
                 (fun e1  ->
                    let uu____63266 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____63266
                      (fun c1  ->
                         let uu____63272 =
                           let uu____63277 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____63277 tacopt  in
                         FStar_Util.bind_opt uu____63272
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _63292  ->
                                   FStar_Pervasives_Native.Some _63292)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _63312  -> FStar_Pervasives_Native.Some _63312)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____63313 ->
               (if w
                then
                  (let uu____63328 =
                     let uu____63334 =
                       let uu____63336 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____63336
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____63334)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____63328)
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
    let uu____63365 =
      let uu____63370 =
        let uu____63371 =
          let uu____63380 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____63380  in
        let uu____63382 =
          let uu____63393 =
            let uu____63402 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____63402  in
          let uu____63403 =
            let uu____63414 =
              let uu____63423 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____63423  in
            [uu____63414]  in
          uu____63393 :: uu____63403  in
        uu____63371 :: uu____63382  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____63370
       in
    uu____63365 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63474 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63474 with
    | (hd1,args) ->
        let uu____63519 =
          let uu____63532 =
            let uu____63533 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63533.FStar_Syntax_Syntax.n  in
          (uu____63532, args)  in
        (match uu____63519 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____63548)::(idx,uu____63550)::(s,uu____63552)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____63597 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____63597
               (fun nm1  ->
                  let uu____63607 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____63607
                    (fun idx1  ->
                       let uu____63613 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____63613
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _63620  ->
                                 FStar_Pervasives_Native.Some _63620)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____63621 ->
             (if w
              then
                (let uu____63636 =
                   let uu____63642 =
                     let uu____63644 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____63644
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____63642)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____63636)
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
        let uu____63670 =
          let uu____63675 =
            let uu____63676 =
              let uu____63685 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____63685  in
            let uu____63686 =
              let uu____63697 =
                let uu____63706 =
                  let uu____63707 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____63707 rng md  in
                FStar_Syntax_Syntax.as_arg uu____63706  in
              [uu____63697]  in
            uu____63676 :: uu____63686  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____63675
           in
        uu____63670 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____63743 =
          let uu____63748 =
            let uu____63749 =
              let uu____63758 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____63758  in
            let uu____63759 =
              let uu____63770 =
                let uu____63779 = embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____63779  in
              [uu____63770]  in
            uu____63749 :: uu____63759  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____63748
           in
        uu____63743 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___1128_63804 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1128_63804.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1128_63804.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____63823 = FStar_Syntax_Util.head_and_args t1  in
    match uu____63823 with
    | (hd1,args) ->
        let uu____63868 =
          let uu____63881 =
            let uu____63882 = FStar_Syntax_Util.un_uinst hd1  in
            uu____63882.FStar_Syntax_Syntax.n  in
          (uu____63881, args)  in
        (match uu____63868 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____63897)::(md,uu____63899)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____63934 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____63934
               (fun t3  ->
                  let uu____63940 =
                    let uu____63945 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____63945 md  in
                  FStar_Util.bind_opt uu____63940
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _63960  -> FStar_Pervasives_Native.Some _63960)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____63965)::(post,uu____63967)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____64002 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____64002
               (fun pre1  ->
                  let uu____64008 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____64008
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _64015  -> FStar_Pervasives_Native.Some _64015)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _64033  -> FStar_Pervasives_Native.Some _64033)
               FStar_Reflection_Data.C_Unknown
         | uu____64034 ->
             (if w
              then
                (let uu____64049 =
                   let uu____64055 =
                     let uu____64057 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____64057
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64055)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64049)
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
    let uu___1175_64082 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1175_64082.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1175_64082.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64103 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64103 with
    | (hd1,args) ->
        let uu____64148 =
          let uu____64163 =
            let uu____64164 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64164.FStar_Syntax_Syntax.n  in
          (uu____64163, args)  in
        (match uu____64148 with
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
         | uu____64236 ->
             (if w
              then
                (let uu____64253 =
                   let uu____64259 =
                     let uu____64261 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____64261
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____64259)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____64253)
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
    let uu____64298 =
      let uu____64299 = FStar_Syntax_Subst.compress t  in
      uu____64299.FStar_Syntax_Syntax.n  in
    match uu____64298 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____64305;
          FStar_Syntax_Syntax.rng = uu____64306;_}
        ->
        let uu____64309 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____64309
    | uu____64310 ->
        (if w
         then
           (let uu____64313 =
              let uu____64319 =
                let uu____64321 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____64321
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____64319)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____64313)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____64361 uu____64362 =
    let uu____64364 =
      let uu____64370 = FStar_Ident.range_of_id i  in
      let uu____64371 = FStar_Ident.text_of_id i  in
      (uu____64370, uu____64371)  in
    embed repr rng uu____64364  in
  let unembed_ident t w uu____64398 =
    let uu____64403 = unembed' w repr t  in
    match uu____64403 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____64427 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____64427
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____64434 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____64434
  
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
        let uu____64473 =
          let uu____64478 =
            let uu____64479 =
              let uu____64488 = embed FStar_Syntax_Embeddings.e_bool rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____64488  in
            let uu____64490 =
              let uu____64501 =
                let uu____64510 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____64510  in
              let uu____64511 =
                let uu____64522 =
                  let uu____64531 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____64531  in
                let uu____64534 =
                  let uu____64545 =
                    let uu____64554 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____64554  in
                  let uu____64555 =
                    let uu____64566 =
                      let uu____64575 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____64575  in
                    [uu____64566]  in
                  uu____64545 :: uu____64555  in
                uu____64522 :: uu____64534  in
              uu____64501 :: uu____64511  in
            uu____64479 :: uu____64490  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____64478
           in
        uu____64473 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____64626 =
          let uu____64631 =
            let uu____64632 =
              let uu____64641 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64641  in
            let uu____64645 =
              let uu____64656 =
                let uu____64665 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____64665  in
              [uu____64656]  in
            uu____64632 :: uu____64645  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____64631
           in
        uu____64626 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____64707 =
          let uu____64712 =
            let uu____64713 =
              let uu____64722 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____64722  in
            let uu____64726 =
              let uu____64737 =
                let uu____64746 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____64746  in
              let uu____64749 =
                let uu____64760 =
                  let uu____64769 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____64769  in
                let uu____64770 =
                  let uu____64781 =
                    let uu____64790 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____64790  in
                  let uu____64791 =
                    let uu____64802 =
                      let uu____64811 =
                        let uu____64812 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____64812 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____64811  in
                    [uu____64802]  in
                  uu____64781 :: uu____64791  in
                uu____64760 :: uu____64770  in
              uu____64737 :: uu____64749  in
            uu____64713 :: uu____64726  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____64712
           in
        uu____64707 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___1251_64876 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___1251_64876.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars =
            (uu___1251_64876.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____64895 = FStar_Syntax_Util.head_and_args t1  in
    match uu____64895 with
    | (hd1,args) ->
        let uu____64940 =
          let uu____64953 =
            let uu____64954 = FStar_Syntax_Util.un_uinst hd1  in
            uu____64954.FStar_Syntax_Syntax.n  in
          (uu____64953, args)  in
        (match uu____64940 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____64969)::(us,uu____64971)::(bs,uu____64973)::
            (t2,uu____64975)::(dcs,uu____64977)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____65042 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____65042
               (fun nm1  ->
                  let uu____65060 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____65060
                    (fun us1  ->
                       let uu____65074 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____65074
                         (fun bs1  ->
                            let uu____65080 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____65080
                              (fun t3  ->
                                 let uu____65086 =
                                   let uu____65094 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____65094 dcs  in
                                 FStar_Util.bind_opt uu____65086
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _65124  ->
                                           FStar_Pervasives_Native.Some
                                             _65124)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____65133)::(fvar1,uu____65135)::(univs1,uu____65137)::
            (ty,uu____65139)::(t2,uu____65141)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____65206 = unembed' w FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____65206
               (fun r1  ->
                  let uu____65216 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____65216
                    (fun fvar2  ->
                       let uu____65222 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____65222
                         (fun univs2  ->
                            let uu____65236 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____65236
                              (fun ty1  ->
                                 let uu____65242 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____65242
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _65249  ->
                                           FStar_Pervasives_Native.Some
                                             _65249)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____65268 ->
             (if w
              then
                (let uu____65283 =
                   let uu____65289 =
                     let uu____65291 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____65291
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65289)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65283)
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
          let uu____65317 =
            let uu____65322 =
              let uu____65323 =
                let uu____65332 =
                  let uu____65333 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____65333  in
                FStar_Syntax_Syntax.as_arg uu____65332  in
              [uu____65323]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____65322
             in
          uu____65317 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____65353 =
            let uu____65358 =
              let uu____65359 =
                let uu____65368 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____65368  in
              let uu____65369 =
                let uu____65380 =
                  let uu____65389 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____65389  in
                [uu____65380]  in
              uu____65359 :: uu____65369  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____65358
             in
          uu____65353 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___1326_65414 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___1326_65414.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___1326_65414.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____65435 = FStar_Syntax_Util.head_and_args t1  in
    match uu____65435 with
    | (hd1,args) ->
        let uu____65480 =
          let uu____65493 =
            let uu____65494 = FStar_Syntax_Util.un_uinst hd1  in
            uu____65494.FStar_Syntax_Syntax.n  in
          (uu____65493, args)  in
        (match uu____65480 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____65524)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____65549 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____65549
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _65556  -> FStar_Pervasives_Native.Some _65556)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____65559)::(e2,uu____65561)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____65596 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____65596
               (fun e11  ->
                  let uu____65602 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____65602
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _65609  -> FStar_Pervasives_Native.Some _65609)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____65610 ->
             (if w
              then
                (let uu____65625 =
                   let uu____65631 =
                     let uu____65633 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____65633
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____65631)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                   uu____65625)
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
    let uu____65657 =
      let uu____65662 =
        let uu____65663 =
          let uu____65672 =
            let uu____65673 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____65673  in
          FStar_Syntax_Syntax.as_arg uu____65672  in
        [uu____65663]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____65662
       in
    uu____65657 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65697 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____65697 with
    | (bv,aq) ->
        let uu____65704 =
          let uu____65709 =
            let uu____65710 =
              let uu____65719 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____65719  in
            let uu____65720 =
              let uu____65731 =
                let uu____65740 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____65740  in
              [uu____65731]  in
            uu____65710 :: uu____65720  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____65709
           in
        uu____65704 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65772 =
      let uu____65777 =
        let uu____65778 =
          let uu____65787 =
            let uu____65788 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____65795 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____65788 i.FStar_Syntax_Syntax.rng uu____65795  in
          FStar_Syntax_Syntax.as_arg uu____65787  in
        [uu____65778]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____65777
       in
    uu____65772 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65825 =
      let uu____65830 =
        let uu____65831 =
          let uu____65840 =
            let uu____65841 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____65841  in
          FStar_Syntax_Syntax.as_arg uu____65840  in
        [uu____65831]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____65830
       in
    uu____65825 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____65871 =
      let uu____65876 =
        let uu____65877 =
          let uu____65886 =
            let uu____65887 = FStar_Reflection_Basic.inspect_sigelt sigelt
               in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____65887  in
          FStar_Syntax_Syntax.as_arg uu____65886  in
        [uu____65877]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____65876
       in
    uu____65871 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  