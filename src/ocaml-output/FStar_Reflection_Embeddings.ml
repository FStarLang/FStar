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
          let uu____405 = f x  in
          FStar_Util.bind_opt uu____405
            (fun x1  ->
               let uu____413 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____413
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
        let uu____482 =
          mapM_opt
            (fun uu____495  ->
               match uu____495 with
               | (bv,e) ->
                   let uu____504 = unembed_term w e  in
                   FStar_Util.bind_opt uu____504
                     (fun e1  ->
                        FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.NT (bv, e1)))) aq1
           in
        FStar_Util.bind_opt uu____482
          (fun s  ->
             let uu____518 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____518)
         in
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____520 =
        let uu____521 = FStar_Syntax_Subst.compress t1  in
        uu____521.FStar_Syntax_Syntax.n  in
      match uu____520 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____532 ->
          (if w
           then
             (let uu____535 =
                let uu____541 =
                  let uu____543 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____543  in
                (FStar_Errors.Warning_NotEmbedded, uu____541)  in
              FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____535)
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
          let uu____578 =
            let uu____583 =
              let uu____584 =
                let uu____593 = embed e_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____593  in
              [uu____584]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____583
             in
          uu____578 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___106_610 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___106_610.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___106_610.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____631 = FStar_Syntax_Util.head_and_args t1  in
    match uu____631 with
    | (hd1,args) ->
        let uu____676 =
          let uu____691 =
            let uu____692 = FStar_Syntax_Util.un_uinst hd1  in
            uu____692.FStar_Syntax_Syntax.n  in
          (uu____691, args)  in
        (match uu____676 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____747)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____782 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____782
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____787 ->
             (if w
              then
                (let uu____804 =
                   let uu____810 =
                     let uu____812 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____812
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____810)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____804)
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
    let uu____852 =
      let uu____853 = FStar_Syntax_Subst.compress t  in
      uu____853.FStar_Syntax_Syntax.n  in
    match uu____852 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ;
          FStar_Syntax_Syntax.ltyp = uu____859;
          FStar_Syntax_Syntax.rng = uu____860;_}
        ->
        let uu____863 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____863
    | uu____864 ->
        (if w
         then
           (let uu____867 =
              let uu____873 =
                let uu____875 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____875  in
              (FStar_Errors.Warning_NotEmbedded, uu____873)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____867)
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
    let uu____912 =
      let uu____913 = FStar_Syntax_Subst.compress t  in
      uu____913.FStar_Syntax_Syntax.n  in
    match uu____912 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ;
          FStar_Syntax_Syntax.ltyp = uu____919;
          FStar_Syntax_Syntax.rng = uu____920;_}
        ->
        let uu____923 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____923
    | uu____924 ->
        (if w
         then
           (let uu____927 =
              let uu____933 =
                let uu____935 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____935  in
              (FStar_Errors.Warning_NotEmbedded, uu____933)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____927)
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
    let uu____972 =
      let uu____973 = FStar_Syntax_Subst.compress t  in
      uu____973.FStar_Syntax_Syntax.n  in
    match uu____972 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ;
          FStar_Syntax_Syntax.ltyp = uu____979;
          FStar_Syntax_Syntax.rng = uu____980;_}
        ->
        let uu____983 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____983
    | uu____984 ->
        (if w
         then
           (let uu____987 =
              let uu____993 =
                let uu____995 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____995  in
              (FStar_Errors.Warning_NotEmbedded, uu____993)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____987)
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
          let uu____1021 =
            let uu____1026 =
              let uu____1027 =
                let uu____1036 =
                  let uu____1037 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____1037  in
                FStar_Syntax_Syntax.as_arg uu____1036  in
              [uu____1027]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____1026
             in
          uu____1021 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____1057 =
            let uu____1062 =
              let uu____1063 =
                let uu____1072 = embed FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____1072  in
              [uu____1063]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____1062
             in
          uu____1057 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Range r ->
          let uu____1091 =
            let uu____1096 =
              let uu____1097 =
                let uu____1106 = embed FStar_Syntax_Embeddings.e_range rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____1106  in
              [uu____1097]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.t
              uu____1096
             in
          uu____1091 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_Reify  ->
          FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.t
      | FStar_Reflection_Data.C_Reflect ns ->
          let uu____1124 =
            let uu____1129 =
              let uu____1130 =
                let uu____1139 =
                  embed FStar_Syntax_Embeddings.e_string_list rng ns  in
                FStar_Syntax_Syntax.as_arg uu____1139  in
              [uu____1130]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.t
              uu____1129
             in
          uu____1124 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___195_1159 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___195_1159.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___195_1159.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1180 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1180 with
    | (hd1,args) ->
        let uu____1225 =
          let uu____1240 =
            let uu____1241 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1241.FStar_Syntax_Syntax.n  in
          (uu____1240, args)  in
        (match uu____1225 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1315)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1350 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____1350
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _1357  -> FStar_Pervasives_Native.Some _1357)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1360)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1395 = unembed' w FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1395
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _1406  -> FStar_Pervasives_Native.Some _1406)
                    (FStar_Reflection_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(r,uu____1409)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid
             ->
             let uu____1444 = unembed' w FStar_Syntax_Embeddings.e_range r
                in
             FStar_Util.bind_opt uu____1444
               (fun r1  ->
                  FStar_All.pipe_left
                    (fun _1451  -> FStar_Pervasives_Native.Some _1451)
                    (FStar_Reflection_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _1473  -> FStar_Pervasives_Native.Some _1473)
               FStar_Reflection_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv,(ns,uu____1476)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid
             ->
             let uu____1511 =
               unembed' w FStar_Syntax_Embeddings.e_string_list ns  in
             FStar_Util.bind_opt uu____1511
               (fun ns1  ->
                  FStar_All.pipe_left
                    (fun _1530  -> FStar_Pervasives_Native.Some _1530)
                    (FStar_Reflection_Data.C_Reflect ns1))
         | uu____1531 ->
             (if w
              then
                (let uu____1548 =
                   let uu____1554 =
                     let uu____1556 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1556
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1554)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1548)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst 
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1569  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1582 =
            let uu____1587 =
              let uu____1588 =
                let uu____1597 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____1597  in
              [uu____1588]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1587
             in
          uu____1582 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1630 =
            let uu____1635 =
              let uu____1636 =
                let uu____1645 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____1645  in
              let uu____1646 =
                let uu____1657 =
                  let uu____1666 =
                    let uu____1667 =
                      let uu____1677 =
                        let uu____1685 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_tuple2 uu____1685
                          FStar_Syntax_Embeddings.e_bool
                         in
                      FStar_Syntax_Embeddings.e_list uu____1677  in
                    embed uu____1667 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1666  in
                [uu____1657]  in
              uu____1636 :: uu____1646  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1635
             in
          uu____1630 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1726 =
            let uu____1731 =
              let uu____1732 =
                let uu____1741 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1741  in
              [uu____1732]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1731
             in
          uu____1726 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1759 =
            let uu____1764 =
              let uu____1765 =
                let uu____1774 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1774  in
              [uu____1765]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1764
             in
          uu____1759 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1793 =
            let uu____1798 =
              let uu____1799 =
                let uu____1808 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____1808  in
              let uu____1809 =
                let uu____1820 =
                  let uu____1829 = embed e_term rng t  in
                  FStar_Syntax_Syntax.as_arg uu____1829  in
                [uu____1820]  in
              uu____1799 :: uu____1809  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1798
             in
          uu____1793 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1872 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1872 with
      | (hd1,args) ->
          let uu____1917 =
            let uu____1930 =
              let uu____1931 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1931.FStar_Syntax_Syntax.n  in
            (uu____1930, args)  in
          (match uu____1917 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1946)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1971 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____1971
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _1978  -> FStar_Pervasives_Native.Some _1978)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1981)::(ps,uu____1983)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____2018 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____2018
                 (fun f1  ->
                    let uu____2024 =
                      let uu____2034 =
                        let uu____2044 =
                          let uu____2052 = e_pattern' ()  in
                          FStar_Syntax_Embeddings.e_tuple2 uu____2052
                            FStar_Syntax_Embeddings.e_bool
                           in
                        FStar_Syntax_Embeddings.e_list uu____2044  in
                      unembed' w uu____2034 ps  in
                    FStar_Util.bind_opt uu____2024
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _2086  -> FStar_Pervasives_Native.Some _2086)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2096)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____2121 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2121
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2128  -> FStar_Pervasives_Native.Some _2128)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____2131)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____2156 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2156
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _2163  -> FStar_Pervasives_Native.Some _2163)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____2166)::(t2,uu____2168)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____2203 = unembed' w e_bv bv  in
               FStar_Util.bind_opt uu____2203
                 (fun bv1  ->
                    let uu____2209 = unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____2209
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _2216  -> FStar_Pervasives_Native.Some _2216)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____2217 ->
               (if w
                then
                  (let uu____2232 =
                     let uu____2238 =
                       let uu____2240 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____2240
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____2238)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____2232)
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
    let uu____2272 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____2272
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)
      FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____2287 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____2287 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____2310 =
            let uu____2315 =
              let uu____2316 =
                let uu____2325 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2325  in
              [uu____2316]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____2315
             in
          uu____2310 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____2343 =
            let uu____2348 =
              let uu____2349 =
                let uu____2358 = embed e_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____2358  in
              [uu____2349]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____2348
             in
          uu____2343 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____2376 =
            let uu____2381 =
              let uu____2382 =
                let uu____2391 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2391  in
              [uu____2382]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____2381
             in
          uu____2376 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____2410 =
            let uu____2415 =
              let uu____2416 =
                let uu____2425 =
                  let uu____2426 = e_term_aq aq  in embed uu____2426 rng hd1
                   in
                FStar_Syntax_Syntax.as_arg uu____2425  in
              let uu____2429 =
                let uu____2440 =
                  let uu____2449 =
                    let uu____2450 = e_argv_aq aq  in embed uu____2450 rng a
                     in
                  FStar_Syntax_Syntax.as_arg uu____2449  in
                [uu____2440]  in
              uu____2416 :: uu____2429  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____2415
             in
          uu____2410 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____2487 =
            let uu____2492 =
              let uu____2493 =
                let uu____2502 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2502  in
              let uu____2503 =
                let uu____2514 =
                  let uu____2523 =
                    let uu____2524 = e_term_aq aq  in embed uu____2524 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2523  in
                [uu____2514]  in
              uu____2493 :: uu____2503  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____2492
             in
          uu____2487 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2553 =
            let uu____2558 =
              let uu____2559 =
                let uu____2568 = embed e_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____2568  in
              let uu____2569 =
                let uu____2580 =
                  let uu____2589 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____2589  in
                [uu____2580]  in
              uu____2559 :: uu____2569  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2558
             in
          uu____2553 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2615 =
            let uu____2620 =
              let uu____2621 =
                let uu____2630 = embed FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2630  in
              [uu____2621]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2620
             in
          uu____2615 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2649 =
            let uu____2654 =
              let uu____2655 =
                let uu____2664 = embed e_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____2664  in
              let uu____2665 =
                let uu____2676 =
                  let uu____2685 =
                    let uu____2686 = e_term_aq aq  in embed uu____2686 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____2685  in
                [uu____2676]  in
              uu____2655 :: uu____2665  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2654
             in
          uu____2649 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2714 =
            let uu____2719 =
              let uu____2720 =
                let uu____2729 = embed e_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____2729  in
              [uu____2720]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2719
             in
          uu____2714 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2748 =
            let uu____2753 =
              let uu____2754 =
                let uu____2763 = embed FStar_Syntax_Embeddings.e_int rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2763  in
              let uu____2764 =
                let uu____2775 =
                  let uu____2784 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2784  in
                [uu____2775]  in
              uu____2754 :: uu____2764  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2753
             in
          uu____2748 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,attrs,b,t1,t2) ->
          let uu____2824 =
            let uu____2829 =
              let uu____2830 =
                let uu____2839 = embed FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2839  in
              let uu____2841 =
                let uu____2852 =
                  let uu____2861 =
                    let uu____2862 = FStar_Syntax_Embeddings.e_list e_term
                       in
                    embed uu____2862 rng attrs  in
                  FStar_Syntax_Syntax.as_arg uu____2861  in
                let uu____2869 =
                  let uu____2880 =
                    let uu____2889 = embed e_bv rng b  in
                    FStar_Syntax_Syntax.as_arg uu____2889  in
                  let uu____2890 =
                    let uu____2901 =
                      let uu____2910 =
                        let uu____2911 = e_term_aq aq  in
                        embed uu____2911 rng t1  in
                      FStar_Syntax_Syntax.as_arg uu____2910  in
                    let uu____2914 =
                      let uu____2925 =
                        let uu____2934 =
                          let uu____2935 = e_term_aq aq  in
                          embed uu____2935 rng t2  in
                        FStar_Syntax_Syntax.as_arg uu____2934  in
                      [uu____2925]  in
                    uu____2901 :: uu____2914  in
                  uu____2880 :: uu____2890  in
                uu____2852 :: uu____2869  in
              uu____2830 :: uu____2841  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2829
             in
          uu____2824 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2992 =
            let uu____2997 =
              let uu____2998 =
                let uu____3007 =
                  let uu____3008 = e_term_aq aq  in embed uu____3008 rng t1
                   in
                FStar_Syntax_Syntax.as_arg uu____3007  in
              let uu____3011 =
                let uu____3022 =
                  let uu____3031 =
                    let uu____3032 =
                      let uu____3041 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____3041  in
                    embed uu____3032 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____3031  in
                [uu____3022]  in
              uu____2998 :: uu____3011  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2997
             in
          uu____2992 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____3089 =
            let uu____3094 =
              let uu____3095 =
                let uu____3104 =
                  let uu____3105 = e_term_aq aq  in embed uu____3105 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3104  in
              let uu____3108 =
                let uu____3119 =
                  let uu____3128 =
                    let uu____3129 = e_term_aq aq  in embed uu____3129 rng t1
                     in
                  FStar_Syntax_Syntax.as_arg uu____3128  in
                let uu____3132 =
                  let uu____3143 =
                    let uu____3152 =
                      let uu____3153 =
                        let uu____3158 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3158  in
                      embed uu____3153 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3152  in
                  [uu____3143]  in
                uu____3119 :: uu____3132  in
              uu____3095 :: uu____3108  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____3094
             in
          uu____3089 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____3202 =
            let uu____3207 =
              let uu____3208 =
                let uu____3217 =
                  let uu____3218 = e_term_aq aq  in embed uu____3218 rng e
                   in
                FStar_Syntax_Syntax.as_arg uu____3217  in
              let uu____3221 =
                let uu____3232 =
                  let uu____3241 = embed e_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____3241  in
                let uu____3242 =
                  let uu____3253 =
                    let uu____3262 =
                      let uu____3263 =
                        let uu____3268 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____3268  in
                      embed uu____3263 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____3262  in
                  [uu____3253]  in
                uu____3232 :: uu____3242  in
              uu____3208 :: uu____3221  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____3207
             in
          uu____3202 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___389_3305 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___389_3305.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___389_3305.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____3323 = FStar_Syntax_Util.head_and_args t  in
      match uu____3323 with
      | (hd1,args) ->
          let uu____3368 =
            let uu____3381 =
              let uu____3382 = FStar_Syntax_Util.un_uinst hd1  in
              uu____3382.FStar_Syntax_Syntax.n  in
            (uu____3381, args)  in
          (match uu____3368 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3397)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____3422 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3422
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3429  -> FStar_Pervasives_Native.Some _3429)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____3432)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____3457 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3457
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _3464  -> FStar_Pervasives_Native.Some _3464)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____3467)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____3492 = unembed' w e_fv f  in
               FStar_Util.bind_opt uu____3492
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _3499  -> FStar_Pervasives_Native.Some _3499)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____3502)::(r,uu____3504)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____3539 = unembed' w e_term l  in
               FStar_Util.bind_opt uu____3539
                 (fun l1  ->
                    let uu____3545 = unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____3545
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _3552  -> FStar_Pervasives_Native.Some _3552)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3555)::(t1,uu____3557)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3592 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3592
                 (fun b1  ->
                    let uu____3598 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3598
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3605  -> FStar_Pervasives_Native.Some _3605)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3608)::(t1,uu____3610)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3645 = unembed' w e_binder b  in
               FStar_Util.bind_opt uu____3645
                 (fun b1  ->
                    let uu____3651 = unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3651
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _3658  -> FStar_Pervasives_Native.Some _3658)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3661)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3686 = unembed' w FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3686
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _3693  -> FStar_Pervasives_Native.Some _3693)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3696)::(t1,uu____3698)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3733 = unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3733
                 (fun b1  ->
                    let uu____3739 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3739
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _3746  -> FStar_Pervasives_Native.Some _3746)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3749)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3774 = unembed' w e_const c  in
               FStar_Util.bind_opt uu____3774
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _3781  -> FStar_Pervasives_Native.Some _3781)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3784)::(l,uu____3786)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3821 = unembed' w FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3821
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _3830  -> FStar_Pervasives_Native.Some _3830)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3833)::(attrs,uu____3835)::(b,uu____3837)::
              (t1,uu____3839)::(t2,uu____3841)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3906 = unembed' w FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3906
                 (fun r1  ->
                    let uu____3916 =
                      let uu____3921 = FStar_Syntax_Embeddings.e_list e_term
                         in
                      unembed' w uu____3921 attrs  in
                    FStar_Util.bind_opt uu____3916
                      (fun attrs1  ->
                         let uu____3935 = unembed' w e_bv b  in
                         FStar_Util.bind_opt uu____3935
                           (fun b1  ->
                              let uu____3941 = unembed' w e_term t1  in
                              FStar_Util.bind_opt uu____3941
                                (fun t11  ->
                                   let uu____3947 = unembed' w e_term t2  in
                                   FStar_Util.bind_opt uu____3947
                                     (fun t21  ->
                                        FStar_All.pipe_left
                                          (fun _3954  ->
                                             FStar_Pervasives_Native.Some
                                               _3954)
                                          (FStar_Reflection_Data.Tv_Let
                                             (r1, attrs1, b1, t11, t21)))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3960)::(brs,uu____3962)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3997 = unembed' w e_term t1  in
               FStar_Util.bind_opt uu____3997
                 (fun t2  ->
                    let uu____4003 =
                      let uu____4008 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      unembed' w uu____4008 brs  in
                    FStar_Util.bind_opt uu____4003
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _4023  -> FStar_Pervasives_Native.Some _4023)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____4028)::(t1,uu____4030)::(tacopt,uu____4032)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____4077 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4077
                 (fun e1  ->
                    let uu____4083 = unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____4083
                      (fun t2  ->
                         let uu____4089 =
                           let uu____4094 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4094 tacopt  in
                         FStar_Util.bind_opt uu____4089
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4109  ->
                                   FStar_Pervasives_Native.Some _4109)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____4114)::(c,uu____4116)::(tacopt,uu____4118)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____4163 = unembed' w e_term e  in
               FStar_Util.bind_opt uu____4163
                 (fun e1  ->
                    let uu____4169 = unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____4169
                      (fun c1  ->
                         let uu____4175 =
                           let uu____4180 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           unembed' w uu____4180 tacopt  in
                         FStar_Util.bind_opt uu____4175
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _4195  ->
                                   FStar_Pervasives_Native.Some _4195)
                                (FStar_Reflection_Data.Tv_AscribedC
                                   (e1, c1, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
               ->
               FStar_All.pipe_left
                 (fun _4215  -> FStar_Pervasives_Native.Some _4215)
                 FStar_Reflection_Data.Tv_Unknown
           | uu____4216 ->
               (if w
                then
                  (let uu____4231 =
                     let uu____4237 =
                       let uu____4239 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____4239
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____4237)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____4231)
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
    let uu____4268 = FStar_Ident.path_of_lid lid  in
    embed FStar_Syntax_Embeddings.e_string_list rng uu____4268  in
  let unembed1 w t =
    let uu____4296 = unembed' w FStar_Syntax_Embeddings.e_string_list t  in
    FStar_Util.map_opt uu____4296
      (fun p  -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos)
     in
  let uu____4313 = FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb_full
    (fun x  -> fun r  -> fun uu____4320  -> fun uu____4321  -> embed1 r x)
    (fun x  -> fun w  -> fun uu____4328  -> unembed1 w x) uu____4313
    FStar_Ident.string_of_lid FStar_Syntax_Syntax.ET_abstract
  
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____4345 =
      let uu____4350 =
        let uu____4351 =
          let uu____4360 =
            embed FStar_Syntax_Embeddings.e_string rng
              bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____4360  in
        let uu____4362 =
          let uu____4373 =
            let uu____4382 =
              embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____4382  in
          let uu____4383 =
            let uu____4394 =
              let uu____4403 =
                embed e_term rng bvv.FStar_Reflection_Data.bv_sort  in
              FStar_Syntax_Syntax.as_arg uu____4403  in
            [uu____4394]  in
          uu____4373 :: uu____4383  in
        uu____4351 :: uu____4362  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____4350
       in
    uu____4345 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4454 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4454 with
    | (hd1,args) ->
        let uu____4499 =
          let uu____4512 =
            let uu____4513 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4513.FStar_Syntax_Syntax.n  in
          (uu____4512, args)  in
        (match uu____4499 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4528)::(idx,uu____4530)::(s,uu____4532)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____4577 = unembed' w FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____4577
               (fun nm1  ->
                  let uu____4587 =
                    unembed' w FStar_Syntax_Embeddings.e_int idx  in
                  FStar_Util.bind_opt uu____4587
                    (fun idx1  ->
                       let uu____4593 = unembed' w e_term s  in
                       FStar_Util.bind_opt uu____4593
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _4600  ->
                                 FStar_Pervasives_Native.Some _4600)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____4601 ->
             (if w
              then
                (let uu____4616 =
                   let uu____4622 =
                     let uu____4624 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____4624
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4622)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4616)
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
        let uu____4650 =
          let uu____4655 =
            let uu____4656 =
              let uu____4665 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4665  in
            let uu____4666 =
              let uu____4677 =
                let uu____4686 =
                  let uu____4687 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4687 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4686  in
              [uu____4677]  in
            uu____4656 :: uu____4666  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____4655
           in
        uu____4650 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_GTotal (t,md) ->
        let uu____4724 =
          let uu____4729 =
            let uu____4730 =
              let uu____4739 = embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____4739  in
            let uu____4740 =
              let uu____4751 =
                let uu____4760 =
                  let uu____4761 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  embed uu____4761 rng md  in
                FStar_Syntax_Syntax.as_arg uu____4760  in
              [uu____4751]  in
            uu____4730 :: uu____4740  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.t
            uu____4729
           in
        uu____4724 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post,pats) ->
        let uu____4795 =
          let uu____4800 =
            let uu____4801 =
              let uu____4810 = embed e_term rng pre  in
              FStar_Syntax_Syntax.as_arg uu____4810  in
            let uu____4811 =
              let uu____4822 =
                let uu____4831 = embed e_term rng post  in
                FStar_Syntax_Syntax.as_arg uu____4831  in
              let uu____4832 =
                let uu____4843 =
                  let uu____4852 = embed e_term rng pats  in
                  FStar_Syntax_Syntax.as_arg uu____4852  in
                [uu____4843]  in
              uu____4822 :: uu____4832  in
            uu____4801 :: uu____4811  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4800
           in
        uu____4795 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Eff (us,eff,res,args) ->
        let uu____4897 =
          let uu____4902 =
            let uu____4903 =
              let uu____4912 = embed FStar_Syntax_Embeddings.e_unit rng ()
                 in
              FStar_Syntax_Syntax.as_arg uu____4912  in
            let uu____4913 =
              let uu____4924 =
                let uu____4933 =
                  embed FStar_Syntax_Embeddings.e_string_list rng eff  in
                FStar_Syntax_Syntax.as_arg uu____4933  in
              let uu____4937 =
                let uu____4948 =
                  let uu____4957 = embed e_term rng res  in
                  FStar_Syntax_Syntax.as_arg uu____4957  in
                let uu____4958 =
                  let uu____4969 =
                    let uu____4978 =
                      let uu____4979 = FStar_Syntax_Embeddings.e_list e_argv
                         in
                      embed uu____4979 rng args  in
                    FStar_Syntax_Syntax.as_arg uu____4978  in
                  [uu____4969]  in
                uu____4948 :: uu____4958  in
              uu____4924 :: uu____4937  in
            uu____4903 :: uu____4913  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.t
            uu____4902
           in
        uu____4897 FStar_Pervasives_Native.None rng
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5044 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5044 with
    | (hd1,args) ->
        let uu____5089 =
          let uu____5102 =
            let uu____5103 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5103.FStar_Syntax_Syntax.n  in
          (uu____5102, args)  in
        (match uu____5089 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____5118)::(md,uu____5120)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____5155 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____5155
               (fun t3  ->
                  let uu____5161 =
                    let uu____5166 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____5166 md  in
                  FStar_Util.bind_opt uu____5161
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _5181  -> FStar_Pervasives_Native.Some _5181)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____5186)::(md,uu____5188)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_GTotal.FStar_Reflection_Data.lid
             ->
             let uu____5223 = unembed' w e_term t2  in
             FStar_Util.bind_opt uu____5223
               (fun t3  ->
                  let uu____5229 =
                    let uu____5234 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    unembed' w uu____5234 md  in
                  FStar_Util.bind_opt uu____5229
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _5249  -> FStar_Pervasives_Native.Some _5249)
                         (FStar_Reflection_Data.C_GTotal (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____5254)::(post,uu____5256)::(pats,uu____5258)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____5303 = unembed' w e_term pre  in
             FStar_Util.bind_opt uu____5303
               (fun pre1  ->
                  let uu____5309 = unembed' w e_term post  in
                  FStar_Util.bind_opt uu____5309
                    (fun post1  ->
                       let uu____5315 = unembed' w e_term pats  in
                       FStar_Util.bind_opt uu____5315
                         (fun pats1  ->
                            FStar_All.pipe_left
                              (fun _5322  ->
                                 FStar_Pervasives_Native.Some _5322)
                              (FStar_Reflection_Data.C_Lemma
                                 (pre1, post1, pats1)))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(us,uu____5325)::(eff,uu____5327)::(res,uu____5329)::(args1,uu____5331)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Eff.FStar_Reflection_Data.lid
             ->
             let uu____5386 = unembed' w FStar_Syntax_Embeddings.e_unit us
                in
             FStar_Util.bind_opt uu____5386
               (fun us1  ->
                  let uu____5392 =
                    unembed' w FStar_Syntax_Embeddings.e_string_list eff  in
                  FStar_Util.bind_opt uu____5392
                    (fun eff1  ->
                       let uu____5410 = unembed' w e_term res  in
                       FStar_Util.bind_opt uu____5410
                         (fun res1  ->
                            let uu____5416 =
                              let uu____5421 =
                                FStar_Syntax_Embeddings.e_list e_argv  in
                              unembed' w uu____5421 args1  in
                            FStar_Util.bind_opt uu____5416
                              (fun args2  ->
                                 FStar_All.pipe_left
                                   (fun _5436  ->
                                      FStar_Pervasives_Native.Some _5436)
                                   (FStar_Reflection_Data.C_Eff
                                      ([], eff1, res1, args2))))))
         | uu____5441 ->
             (if w
              then
                (let uu____5456 =
                   let uu____5462 =
                     let uu____5464 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____5464
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5462)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5456)
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
    let uu___714_5489 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___714_5489.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___714_5489.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5510 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5510 with
    | (hd1,args) ->
        let uu____5555 =
          let uu____5570 =
            let uu____5571 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5571.FStar_Syntax_Syntax.n  in
          (uu____5570, args)  in
        (match uu____5555 with
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
         | uu____5643 ->
             (if w
              then
                (let uu____5660 =
                   let uu____5666 =
                     let uu____5668 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____5668
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5666)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5660)
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
    let uu____5705 =
      let uu____5706 = FStar_Syntax_Subst.compress t  in
      uu____5706.FStar_Syntax_Syntax.n  in
    match uu____5705 with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ;
          FStar_Syntax_Syntax.ltyp = uu____5712;
          FStar_Syntax_Syntax.rng = uu____5713;_}
        ->
        let uu____5716 = FStar_Dyn.undyn b  in
        FStar_Pervasives_Native.Some uu____5716
    | uu____5717 ->
        (if w
         then
           (let uu____5720 =
              let uu____5726 =
                let uu____5728 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____5728
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____5726)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____5720)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt 
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident i rng uu____5768 uu____5769 =
    let uu____5771 =
      let uu____5777 = FStar_Ident.range_of_id i  in
      let uu____5778 = FStar_Ident.text_of_id i  in (uu____5777, uu____5778)
       in
    embed repr rng uu____5771  in
  let unembed_ident t w uu____5805 =
    let uu____5810 = unembed' w repr t  in
    match uu____5810 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____5834 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____5834
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____5841 = FStar_Syntax_Embeddings.emb_typ_of repr  in
  FStar_Syntax_Embeddings.mk_emb_full embed_ident unembed_ident
    FStar_Reflection_Data.fstar_refl_ident FStar_Ident.text_of_id uu____5841
  
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
        let uu____5880 =
          let uu____5885 =
            let uu____5886 =
              let uu____5895 = embed FStar_Syntax_Embeddings.e_bool rng r  in
              FStar_Syntax_Syntax.as_arg uu____5895  in
            let uu____5897 =
              let uu____5908 =
                let uu____5917 = embed e_fv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____5917  in
              let uu____5918 =
                let uu____5929 =
                  let uu____5938 = embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____5938  in
                let uu____5941 =
                  let uu____5952 =
                    let uu____5961 = embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____5961  in
                  let uu____5962 =
                    let uu____5973 =
                      let uu____5982 = embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____5982  in
                    [uu____5973]  in
                  uu____5952 :: uu____5962  in
                uu____5929 :: uu____5941  in
              uu____5908 :: uu____5918  in
            uu____5886 :: uu____5897  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____5885
           in
        uu____5880 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____6033 =
          let uu____6038 =
            let uu____6039 =
              let uu____6048 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____6048  in
            let uu____6052 =
              let uu____6063 =
                let uu____6072 = embed e_term rng ty  in
                FStar_Syntax_Syntax.as_arg uu____6072  in
              [uu____6063]  in
            uu____6039 :: uu____6052  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____6038
           in
        uu____6033 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____6114 =
          let uu____6119 =
            let uu____6120 =
              let uu____6129 =
                embed FStar_Syntax_Embeddings.e_string_list rng nm  in
              FStar_Syntax_Syntax.as_arg uu____6129  in
            let uu____6133 =
              let uu____6144 =
                let uu____6153 = embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____6153  in
              let uu____6156 =
                let uu____6167 =
                  let uu____6176 = embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____6176  in
                let uu____6177 =
                  let uu____6188 =
                    let uu____6197 = embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____6197  in
                  let uu____6198 =
                    let uu____6209 =
                      let uu____6218 =
                        let uu____6219 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        embed uu____6219 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____6218  in
                    [uu____6209]  in
                  uu____6188 :: uu____6198  in
                uu____6167 :: uu____6177  in
              uu____6144 :: uu____6156  in
            uu____6120 :: uu____6133  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____6119
           in
        uu____6114 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___790_6283 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___790_6283.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___790_6283.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6302 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6302 with
    | (hd1,args) ->
        let uu____6347 =
          let uu____6360 =
            let uu____6361 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6361.FStar_Syntax_Syntax.n  in
          (uu____6360, args)  in
        (match uu____6347 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____6376)::(us,uu____6378)::(bs,uu____6380)::(t2,uu____6382)::
            (dcs,uu____6384)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____6449 =
               unembed' w FStar_Syntax_Embeddings.e_string_list nm  in
             FStar_Util.bind_opt uu____6449
               (fun nm1  ->
                  let uu____6467 = unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____6467
                    (fun us1  ->
                       let uu____6481 = unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____6481
                         (fun bs1  ->
                            let uu____6487 = unembed' w e_term t2  in
                            FStar_Util.bind_opt uu____6487
                              (fun t3  ->
                                 let uu____6493 =
                                   let uu____6501 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   unembed' w uu____6501 dcs  in
                                 FStar_Util.bind_opt uu____6493
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _6531  ->
                                           FStar_Pervasives_Native.Some _6531)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____6540)::(fvar1,uu____6542)::(univs1,uu____6544)::
            (ty,uu____6546)::(t2,uu____6548)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____6613 = unembed' w FStar_Syntax_Embeddings.e_bool r  in
             FStar_Util.bind_opt uu____6613
               (fun r1  ->
                  let uu____6623 = unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____6623
                    (fun fvar2  ->
                       let uu____6629 = unembed' w e_univ_names univs1  in
                       FStar_Util.bind_opt uu____6629
                         (fun univs2  ->
                            let uu____6643 = unembed' w e_term ty  in
                            FStar_Util.bind_opt uu____6643
                              (fun ty1  ->
                                 let uu____6649 = unembed' w e_term t2  in
                                 FStar_Util.bind_opt uu____6649
                                   (fun t3  ->
                                      FStar_All.pipe_left
                                        (fun _6656  ->
                                           FStar_Pervasives_Native.Some _6656)
                                        (FStar_Reflection_Data.Sg_Let
                                           (r1, fvar2, univs2, ty1, t3)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____6675 ->
             (if w
              then
                (let uu____6690 =
                   let uu____6696 =
                     let uu____6698 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____6698
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____6696)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____6690)
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
          let uu____6724 =
            let uu____6729 =
              let uu____6730 =
                let uu____6739 =
                  let uu____6740 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____6740  in
                FStar_Syntax_Syntax.as_arg uu____6739  in
              [uu____6730]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____6729
             in
          uu____6724 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____6760 =
            let uu____6765 =
              let uu____6766 =
                let uu____6775 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____6775  in
              let uu____6776 =
                let uu____6787 =
                  let uu____6796 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____6796  in
                [uu____6787]  in
              uu____6766 :: uu____6776  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____6765
             in
          uu____6760 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___865_6821 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___865_6821.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___865_6821.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____6842 = FStar_Syntax_Util.head_and_args t1  in
    match uu____6842 with
    | (hd1,args) ->
        let uu____6887 =
          let uu____6900 =
            let uu____6901 = FStar_Syntax_Util.un_uinst hd1  in
            uu____6901.FStar_Syntax_Syntax.n  in
          (uu____6900, args)  in
        (match uu____6887 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____6931)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____6956 = unembed' w FStar_Syntax_Embeddings.e_int i  in
             FStar_Util.bind_opt uu____6956
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _6963  -> FStar_Pervasives_Native.Some _6963)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____6966)::(e2,uu____6968)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____7003 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____7003
               (fun e11  ->
                  let uu____7009 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____7009
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _7016  -> FStar_Pervasives_Native.Some _7016)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____7017 ->
             (if w
              then
                (let uu____7032 =
                   let uu____7038 =
                     let uu____7040 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____7040
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____7038)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____7032)
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
          let uu____7077 =
            let uu____7082 =
              let uu____7083 =
                let uu____7092 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7092  in
              [uu____7083]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.t
              uu____7082
             in
          uu____7077 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Discriminator l ->
          let uu____7110 =
            let uu____7115 =
              let uu____7116 =
                let uu____7125 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7125  in
              [uu____7116]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.t
              uu____7115
             in
          uu____7110 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Action l ->
          let uu____7143 =
            let uu____7148 =
              let uu____7149 =
                let uu____7158 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7158  in
              [uu____7149]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.t
              uu____7148
             in
          uu____7143 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Projector (l,i) ->
          let uu____7177 =
            let uu____7182 =
              let uu____7183 =
                let uu____7192 = embed e_lid rng l  in
                FStar_Syntax_Syntax.as_arg uu____7192  in
              let uu____7193 =
                let uu____7204 =
                  let uu____7213 = embed e_ident rng i  in
                  FStar_Syntax_Syntax.as_arg uu____7213  in
                [uu____7204]  in
              uu____7183 :: uu____7193  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.t
              uu____7182
             in
          uu____7177 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordType (ids1,ids2) ->
          let uu____7248 =
            let uu____7253 =
              let uu____7254 =
                let uu____7263 =
                  let uu____7264 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7264 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____7263  in
              let uu____7271 =
                let uu____7282 =
                  let uu____7291 =
                    let uu____7292 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____7292 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____7291  in
                [uu____7282]  in
              uu____7254 :: uu____7271  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.t
              uu____7253
             in
          uu____7248 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.RecordConstructor (ids1,ids2) ->
          let uu____7333 =
            let uu____7338 =
              let uu____7339 =
                let uu____7348 =
                  let uu____7349 = FStar_Syntax_Embeddings.e_list e_ident  in
                  embed uu____7349 rng ids1  in
                FStar_Syntax_Syntax.as_arg uu____7348  in
              let uu____7356 =
                let uu____7367 =
                  let uu____7376 =
                    let uu____7377 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    embed uu____7377 rng ids2  in
                  FStar_Syntax_Syntax.as_arg uu____7376  in
                [uu____7367]  in
              uu____7339 :: uu____7356  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.t
              uu____7338
             in
          uu____7333 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___941_7408 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___941_7408.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___941_7408.FStar_Syntax_Syntax.vars)
    }  in
  let unembed1 w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____7429 = FStar_Syntax_Util.head_and_args t1  in
    match uu____7429 with
    | (hd1,args) ->
        let uu____7474 =
          let uu____7487 =
            let uu____7488 = FStar_Syntax_Util.un_uinst hd1  in
            uu____7488.FStar_Syntax_Syntax.n  in
          (uu____7487, args)  in
        (match uu____7474 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7773)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Reflectable.FStar_Reflection_Data.lid
             ->
             let uu____7798 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7798
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7805  -> FStar_Pervasives_Native.Some _7805)
                    (FStar_Reflection_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7808)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Discriminator.FStar_Reflection_Data.lid
             ->
             let uu____7833 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7833
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7840  -> FStar_Pervasives_Native.Some _7840)
                    (FStar_Reflection_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____7843)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Action.FStar_Reflection_Data.lid
             ->
             let uu____7868 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7868
               (fun l1  ->
                  FStar_All.pipe_left
                    (fun _7875  -> FStar_Pervasives_Native.Some _7875)
                    (FStar_Reflection_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____7878)::(i,uu____7880)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_Projector.FStar_Reflection_Data.lid
             ->
             let uu____7915 = unembed' w e_lid l  in
             FStar_Util.bind_opt uu____7915
               (fun l1  ->
                  let uu____7921 = unembed' w e_ident i  in
                  FStar_Util.bind_opt uu____7921
                    (fun i1  ->
                       FStar_All.pipe_left
                         (fun _7928  -> FStar_Pervasives_Native.Some _7928)
                         (FStar_Reflection_Data.Projector (l1, i1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____7931)::(ids2,uu____7933)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordType.FStar_Reflection_Data.lid
             ->
             let uu____7968 =
               let uu____7973 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____7973 ids1  in
             FStar_Util.bind_opt uu____7968
               (fun ids11  ->
                  let uu____7987 =
                    let uu____7992 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____7992 ids2  in
                  FStar_Util.bind_opt uu____7987
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _8007  -> FStar_Pervasives_Native.Some _8007)
                         (FStar_Reflection_Data.RecordType (ids11, ids21))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(ids1,uu____8014)::(ids2,uu____8016)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_qual_RecordConstructor.FStar_Reflection_Data.lid
             ->
             let uu____8051 =
               let uu____8056 = FStar_Syntax_Embeddings.e_list e_ident  in
               unembed' w uu____8056 ids1  in
             FStar_Util.bind_opt uu____8051
               (fun ids11  ->
                  let uu____8070 =
                    let uu____8075 = FStar_Syntax_Embeddings.e_list e_ident
                       in
                    unembed' w uu____8075 ids2  in
                  FStar_Util.bind_opt uu____8070
                    (fun ids21  ->
                       FStar_All.pipe_left
                         (fun _8090  -> FStar_Pervasives_Native.Some _8090)
                         (FStar_Reflection_Data.RecordConstructor
                            (ids11, ids21))))
         | uu____8095 ->
             (if w
              then
                (let uu____8110 =
                   let uu____8116 =
                     let uu____8118 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded qualifier: %s"
                       uu____8118
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____8116)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____8110)
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
    let uu____8136 =
      let uu____8141 =
        let uu____8142 =
          let uu____8151 =
            let uu____8152 = FStar_Reflection_Basic.inspect_bv bv  in
            embed e_bv_view i.FStar_Syntax_Syntax.rng uu____8152  in
          FStar_Syntax_Syntax.as_arg uu____8151  in
        [uu____8142]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____8141
       in
    uu____8136 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8176 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____8176 with
    | (bv,aq) ->
        let uu____8183 =
          let uu____8188 =
            let uu____8189 =
              let uu____8198 = embed e_bv i.FStar_Syntax_Syntax.rng bv  in
              FStar_Syntax_Syntax.as_arg uu____8198  in
            let uu____8199 =
              let uu____8210 =
                let uu____8219 = embed e_aqualv i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____8219  in
              [uu____8210]  in
            uu____8189 :: uu____8199  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____8188
           in
        uu____8183 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8251 =
      let uu____8256 =
        let uu____8257 =
          let uu____8266 =
            let uu____8267 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____8274 = FStar_Reflection_Basic.inspect_fv fv  in
            embed uu____8267 i.FStar_Syntax_Syntax.rng uu____8274  in
          FStar_Syntax_Syntax.as_arg uu____8266  in
        [uu____8257]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____8256
       in
    uu____8251 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____8304 =
      let uu____8309 =
        let uu____8310 =
          let uu____8319 =
            let uu____8320 = FStar_Reflection_Basic.inspect_comp comp  in
            embed e_comp_view i.FStar_Syntax_Syntax.rng uu____8320  in
          FStar_Syntax_Syntax.as_arg uu____8319  in
        [uu____8310]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____8309
       in
    uu____8304 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
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
    let uu____8356 =
      let uu____8361 =
        let uu____8362 =
          let uu____8371 =
            let uu____8372 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____8372  in
          FStar_Syntax_Syntax.as_arg uu____8371  in
        [uu____8362]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____8361
       in
    uu____8356 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  